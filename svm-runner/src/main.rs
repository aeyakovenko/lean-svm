use {
    litesvm::LiteSVM,
    sha2::{Digest, Sha256},
    solana_account::Account,
    solana_address::{address, Address},
    solana_clock::Clock,
    solana_instruction::{account_meta::AccountMeta, Instruction},
    solana_keypair::Keypair,
    solana_message::Message,
    solana_signer::Signer,
    solana_transaction::Transaction,
    std::path::PathBuf,
};

const SPL_TOKEN_ID: Address = address!("TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA");
const SPL_TOKEN_2022_ID: Address = address!("TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb");
const SYSTEM_PROGRAM_ID: Address = address!("11111111111111111111111111111111");

fn load_so(name: &str) -> Vec<u8> {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("build")
        .join(name);
    std::fs::read(&path).unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()))
}

fn send_ix(
    svm: &mut LiteSVM,
    payer: &Keypair,
    extra_signers: &[&Keypair],
    ix: Instruction,
) -> litesvm::types::TransactionResult {
    let blockhash = svm.latest_blockhash();
    let msg = Message::new(&[ix], Some(&payer.pubkey()));
    let mut signers: Vec<&Keypair> = vec![payer];
    signers.extend_from_slice(extra_signers);
    let tx = Transaction::new(&signers, msg, blockhash);
    svm.send_transaction(tx)
}

/// Create and initialize a real SPL Token or SPL Token-2022 Mint (zero extra crate deps!).
fn create_mint(
    svm: &mut LiteSVM,
    payer: &Keypair,
    token_prog: Address,
    mint_auth: Address,
    decimals: u8,
) -> Address {
    let mint_addr = Address::new_unique();
    svm.set_account(
        mint_addr,
        Account {
            lamports: 10_000_000,
            data: vec![0u8; 82],
            owner: token_prog,
            ..Default::default()
        },
    )
    .unwrap();
    let mut data = Vec::with_capacity(35);
    data.push(20u8); // InitializeMint2
    data.push(decimals);
    data.extend_from_slice(mint_auth.as_ref());
    data.push(0u8); // COption::None freeze authority
    let ix = Instruction {
        program_id: token_prog,
        accounts: vec![AccountMeta::new(mint_addr, false)],
        data,
    };
    send_ix(svm, payer, &[], ix).expect("InitializeMint2 failed");
    mint_addr
}

/// Create and initialize a real SPL Token or SPL Token-2022 TokenAccount.
fn create_token_account(
    svm: &mut LiteSVM,
    payer: &Keypair,
    token_prog: Address,
    mint: Address,
    owner: Address,
) -> Address {
    let acc_addr = Address::new_unique();
    svm.set_account(
        acc_addr,
        Account {
            lamports: 10_000_000,
            data: vec![0u8; 165],
            owner: token_prog,
            ..Default::default()
        },
    )
    .unwrap();
    let mut data = Vec::with_capacity(33);
    data.push(18u8); // InitializeAccount3
    data.extend_from_slice(owner.as_ref());
    let ix = Instruction {
        program_id: token_prog,
        accounts: vec![
            AccountMeta::new(acc_addr, false),
            AccountMeta::new_readonly(mint, false),
        ],
        data,
    };
    send_ix(svm, payer, &[], ix).expect("InitializeAccount3 failed");
    acc_addr
}

/// Mint SPL Token or Token-2022 tokens into `dest`.
fn mint_tokens(
    svm: &mut LiteSVM,
    payer: &Keypair,
    token_prog: Address,
    mint: Address,
    dest: Address,
    mint_auth: &Keypair,
    amount: u64,
) {
    let mut data = Vec::with_capacity(9);
    data.push(7u8); // MintTo
    data.extend_from_slice(&amount.to_le_bytes());
    let ix = Instruction {
        program_id: token_prog,
        accounts: vec![
            AccountMeta::new(mint, false),
            AccountMeta::new(dest, false),
            AccountMeta::new_readonly(mint_auth.pubkey(), true),
        ],
        data,
    };
    send_ix(svm, payer, &[mint_auth], ix).expect("MintTo failed");
}

fn token_balance(svm: &LiteSVM, acc: &Address) -> u64 {
    let d = &svm.get_account(acc).expect("token acc missing").data;
    u64::from_le_bytes(d[64..72].try_into().unwrap())
}

fn test_noop() {
    let so = load_so("noop.so");
    let mut svm = LiteSVM::new();
    let payer = Keypair::new();
    let program_id = Address::new_unique();
    svm.add_program(program_id, &so).unwrap();
    svm.airdrop(&payer.pubkey(), 1_000_000_000).unwrap();
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };
    let meta = send_ix(&mut svm, &payer, &[], ix).expect("noop failed");
    println!(
        "[PASS] Noop         | .so = {:>6} B | CUs = {:>5}",
        so.len(), meta.compute_units_consumed
    );
}

fn test_counter() {
    let so = load_so("counter.so");
    let mut svm = LiteSVM::new();
    let payer = Keypair::new();
    let counter_kp = Keypair::new();
    let counter_addr = counter_kp.pubkey();
    let program_id = Address::new_unique();
    svm.add_program(program_id, &so).unwrap();
    svm.airdrop(&payer.pubkey(), 1_000_000_000).unwrap();
    svm.set_account(counter_addr, Account {
        lamports: 1_000_000, data: 999u64.to_le_bytes().to_vec(), owner: program_id, ..Default::default()
    }).unwrap();

    let m_init = send_ix(&mut svm, &payer, &[], Instruction {
        program_id, accounts: vec![AccountMeta::new(counter_addr, false)], data: vec![0u8],
    }).expect("init failed");
    assert_eq!(u64::from_le_bytes(svm.get_account(&counter_addr).unwrap().data[0..8].try_into().unwrap()), 0);

    let m_inc = send_ix(&mut svm, &payer, &[], Instruction {
        program_id, accounts: vec![AccountMeta::new(counter_addr, false)], data: vec![1u8],
    }).expect("inc failed");
    assert_eq!(u64::from_le_bytes(svm.get_account(&counter_addr).unwrap().data[0..8].try_into().unwrap()), 1);

    let mut add_data = vec![2u8];
    add_data.extend_from_slice(&41u64.to_le_bytes());
    let m_add = send_ix(&mut svm, &payer, &[], Instruction {
        program_id, accounts: vec![AccountMeta::new(counter_addr, false)], data: add_data,
    }).expect("add failed");
    assert_eq!(u64::from_le_bytes(svm.get_account(&counter_addr).unwrap().data[0..8].try_into().unwrap()), 42);

    // Overflow rejected
    let mut ovf = vec![2u8];
    ovf.extend_from_slice(&u64::MAX.to_le_bytes());
    assert!(send_ix(&mut svm, &payer, &[], Instruction {
        program_id, accounts: vec![AccountMeta::new(counter_addr, false)], data: ovf,
    }).is_err());

    // Unsigned reset rejected, signed reset accepted
    assert!(send_ix(&mut svm, &payer, &[], Instruction {
        program_id, accounts: vec![AccountMeta::new(counter_addr, false)], data: vec![3u8],
    }).is_err());
    send_ix(&mut svm, &payer, &[&counter_kp], Instruction {
        program_id, accounts: vec![AccountMeta::new(counter_addr, true)], data: vec![3u8],
    }).expect("reset failed");
    assert_eq!(u64::from_le_bytes(svm.get_account(&counter_addr).unwrap().data[0..8].try_into().unwrap()), 0);

    println!(
        "[PASS] Counter      | .so = {:>6} B | CUs: init={}, inc={}, add={}",
        so.len(), m_init.compute_units_consumed, m_inc.compute_units_consumed, m_add.compute_units_consumed
    );
}

fn test_vault() {
    let so = load_so("vault.so");
    let mut svm = LiteSVM::new();
    let payer = Keypair::new();
    let auth = Keypair::new();
    let vault_addr = Address::new_unique();
    let dest_addr = Address::new_unique();
    let program_id = Address::new_unique();
    svm.add_program(program_id, &so).unwrap();
    svm.airdrop(&payer.pubkey(), 1_000_000_000).unwrap();
    svm.set_account(vault_addr, Account {
        lamports: 10_000_000, data: auth.pubkey().to_bytes().to_vec(), owner: program_id, ..Default::default()
    }).unwrap();
    svm.set_account(dest_addr, Account {
        lamports: 2_000_000, data: vec![], owner: SYSTEM_PROGRAM_ID, ..Default::default()
    }).unwrap();

    let meta = send_ix(&mut svm, &payer, &[&auth], Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new_readonly(auth.pubkey(), true),
            AccountMeta::new(vault_addr, false),
            AccountMeta::new(dest_addr, false),
        ],
        data: 3_500_000u64.to_le_bytes().to_vec(),
    }).expect("vault transfer failed");
    assert_eq!(svm.get_account(&vault_addr).unwrap().lamports, 6_500_000);
    assert_eq!(svm.get_account(&dest_addr).unwrap().lamports, 5_500_000);
    println!(
        "[PASS] Vault        | .so = {:>6} B | CUs = {:>5} (incl. 100 CU sol_log_)",
        so.len(), meta.compute_units_consumed
    );
}

fn test_hashcheck() {
    let so = load_so("hashcheck.so");
    let mut svm = LiteSVM::new();
    let payer = Keypair::new();
    let state_addr = Address::new_unique();
    let program_id = Address::new_unique();
    svm.add_program(program_id, &so).unwrap();
    svm.airdrop(&payer.pubkey(), 1_000_000_000).unwrap();
    let mut clk = svm.get_sysvar::<Clock>();
    clk.slot = 123_456_789;
    svm.set_sysvar::<Clock>(&clk);
    svm.set_account(state_addr, Account {
        lamports: 1_000_000, data: vec![0u8; 40], owner: program_id, ..Default::default()
    }).unwrap();

    let payload = b"hello from formally verified Lean 4 on Solana SVM!";
    let meta = send_ix(&mut svm, &payer, &[], Instruction {
        program_id, accounts: vec![AccountMeta::new(state_addr, false)], data: payload.to_vec(),
    }).expect("hashcheck failed");
    let acc_data = svm.get_account(&state_addr).unwrap().data;
    let expected: [u8; 32] = Sha256::digest(payload).into();
    assert_eq!(&acc_data[0..32], &expected[..]);
    assert_eq!(u64::from_le_bytes(acc_data[32..40].try_into().unwrap()), 123_456_789);
    println!(
        "[PASS] HashCheck    | .so = {:>6} B | CUs = {:>5} (sha256 + clock + log)",
        so.len(), meta.compute_units_consumed
    );
}

/// Test Multi-SPL Token (Token A) + SPL Token-2022 (Token B) Constant-Product AMM!
fn test_amm() {
    let so = load_so("amm.so");
    let mut svm = LiteSVM::new();
    let payer = Keypair::new();
    let user = Keypair::new();
    let program_id = Address::new_unique();
    svm.add_program(program_id, &so).expect("failed to load amm.so");
    svm.airdrop(&payer.pubkey(), 5_000_000_000).unwrap();
    svm.airdrop(&user.pubkey(), 1_000_000_000).unwrap();

    let pool_addr = Address::new_unique();
    let (pda_auth, bump) = Address::find_program_address(&[b"pool", pool_addr.as_ref()], &program_id);
    svm.set_account(pool_addr, Account {
        lamports: 10_000_000, data: vec![0u8; 120], owner: program_id, ..Default::default()
    }).unwrap();

    // Token A = classic SPL Token (6 decimals), Token B = SPL Token-2022 (9 decimals)!
    let mint_a = create_mint(&mut svm, &payer, SPL_TOKEN_ID, payer.pubkey(), 6);
    let mint_b = create_mint(&mut svm, &payer, SPL_TOKEN_2022_ID, payer.pubkey(), 9);
    let vault_a = create_token_account(&mut svm, &payer, SPL_TOKEN_ID, mint_a, pda_auth);
    let vault_b = create_token_account(&mut svm, &payer, SPL_TOKEN_2022_ID, mint_b, pda_auth);
    let user_a = create_token_account(&mut svm, &payer, SPL_TOKEN_ID, mint_a, user.pubkey());
    let user_b = create_token_account(&mut svm, &payer, SPL_TOKEN_2022_ID, mint_b, user.pubkey());
    mint_tokens(&mut svm, &payer, SPL_TOKEN_ID, mint_a, user_a, &payer, 2_000_000);
    mint_tokens(&mut svm, &payer, SPL_TOKEN_2022_ID, mint_b, user_b, &payer, 2_000_000);

    // 1. InitPool (fee = 30 bps = 0.30%)
    let mut init_data = vec![0u8, bump, 6, 9];
    init_data.extend_from_slice(&30u16.to_le_bytes());
    let m_init = send_ix(&mut svm, &payer, &[], Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(pool_addr, false),
            AccountMeta::new_readonly(vault_a, false),
            AccountMeta::new_readonly(vault_b, false),
        ],
        data: init_data,
    }).expect("AMM InitPool failed");

    // 2. AddLiquidity: 1_000_000 SPL Token A + 1_000_000 Token-2022 B -> LP = isqrt(10^12) = 1_000_000
    let mut add_data = vec![1u8];
    add_data.extend_from_slice(&1_000_000u64.to_le_bytes());
    add_data.extend_from_slice(&1_000_000u64.to_le_bytes());
    add_data.extend_from_slice(&999_999u64.to_le_bytes());
    let m_add = send_ix(&mut svm, &payer, &[&user], Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new_readonly(user.pubkey(), true),
            AccountMeta::new(pool_addr, false),
            AccountMeta::new_readonly(mint_a, false),
            AccountMeta::new_readonly(mint_b, false),
            AccountMeta::new(vault_a, false),
            AccountMeta::new(vault_b, false),
            AccountMeta::new(user_a, false),
            AccountMeta::new(user_b, false),
            AccountMeta::new_readonly(SPL_TOKEN_ID, false),
            AccountMeta::new_readonly(SPL_TOKEN_2022_ID, false),
        ],
        data: add_data,
    }).expect("AMM AddLiquidity failed");
    assert_eq!(token_balance(&svm, &vault_a), 1_000_000);
    assert_eq!(token_balance(&svm, &vault_b), 1_000_000);

    // 3. SwapExactIn: 100_000 SPL Token A -> SPL Token-2022 B!
    // Expected: amtAfterFee = 100_000 * 9970 / 10000 = 99_700; out = 99_700 * 1_000_000 / 1_099_700 = 90_661
    let mut swap_data = vec![2u8, 0u8]; // dir 0 = A -> B
    swap_data.extend_from_slice(&100_000u64.to_le_bytes());
    swap_data.extend_from_slice(&90_000u64.to_le_bytes());
    let m_swap = send_ix(&mut svm, &payer, &[&user], Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new_readonly(user.pubkey(), true),
            AccountMeta::new(pool_addr, false),
            AccountMeta::new_readonly(pda_auth, false),
            AccountMeta::new_readonly(mint_a, false),
            AccountMeta::new_readonly(mint_b, false),
            AccountMeta::new(vault_a, false),
            AccountMeta::new(vault_b, false),
            AccountMeta::new(user_a, false),
            AccountMeta::new(user_b, false),
            AccountMeta::new_readonly(SPL_TOKEN_ID, false),
            AccountMeta::new_readonly(SPL_TOKEN_2022_ID, false),
        ],
        data: swap_data,
    }).expect("AMM SwapExactIn failed");
    assert_eq!(token_balance(&svm, &vault_a), 1_100_000);
    assert_eq!(token_balance(&svm, &vault_b), 1_000_000 - 90_661);
    assert_eq!(token_balance(&svm, &user_b), 1_000_000 + 90_661);

    // 4. RemoveLiquidity: burn 500_000 LP (50% of pool)
    let mut rem_data = vec![3u8];
    rem_data.extend_from_slice(&500_000u64.to_le_bytes());
    rem_data.extend_from_slice(&500_000u64.to_le_bytes());
    rem_data.extend_from_slice(&450_000u64.to_le_bytes());
    let m_rem = send_ix(&mut svm, &payer, &[&user], Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new_readonly(user.pubkey(), true),
            AccountMeta::new(pool_addr, false),
            AccountMeta::new_readonly(pda_auth, false),
            AccountMeta::new_readonly(mint_a, false),
            AccountMeta::new_readonly(mint_b, false),
            AccountMeta::new(vault_a, false),
            AccountMeta::new(vault_b, false),
            AccountMeta::new(user_a, false),
            AccountMeta::new(user_b, false),
            AccountMeta::new_readonly(SPL_TOKEN_ID, false),
            AccountMeta::new_readonly(SPL_TOKEN_2022_ID, false),
        ],
        data: rem_data,
    }).expect("AMM RemoveLiquidity failed");
    assert_eq!(token_balance(&svm, &vault_a), 550_000);

    println!(
        "[PASS] AMM (SPL+2022)| .so = {:>6} B | CUs: init={}, addLiq={}, swap={}, remLiq={}",
        so.len(),
        m_init.compute_units_consumed,
        m_add.compute_units_consumed,
        m_swap.compute_units_consumed,
        m_rem.compute_units_consumed
    );
}

/// Test Collateralized Lending Protocol (SPL Token Collateral + Token-2022 Debt + Clock Interest + Liquidation)!
fn test_lending() {
    let so = load_so("lending.so");
    let mut svm = LiteSVM::new();
    let payer = Keypair::new();
    let borrower = Keypair::new();
    let liquidator = Keypair::new();
    let program_id = Address::new_unique();
    svm.add_program(program_id, &so).expect("failed to load lending.so");
    svm.airdrop(&payer.pubkey(), 5_000_000_000).unwrap();

    let mut clk = svm.get_sysvar::<Clock>();
    clk.slot = 1000;
    svm.set_sysvar::<Clock>(&clk);

    let market_addr = Address::new_unique();
    let obl_addr = Address::new_unique();
    let (pda_auth, bump) = Address::find_program_address(&[b"lend", market_addr.as_ref()], &program_id);
    svm.set_account(market_addr, Account {
        lamports: 10_000_000, data: vec![0u8; 128], owner: program_id, ..Default::default()
    }).unwrap();
    svm.set_account(obl_addr, Account {
        lamports: 10_000_000, data: vec![0u8; 64], owner: program_id, ..Default::default()
    }).unwrap();

    // Collateral = SPL Token (6 dec), Debt = Token-2022 (6 dec)
    let col_mint = create_mint(&mut svm, &payer, SPL_TOKEN_ID, payer.pubkey(), 6);
    let debt_mint = create_mint(&mut svm, &payer, SPL_TOKEN_2022_ID, payer.pubkey(), 6);
    let col_vault = create_token_account(&mut svm, &payer, SPL_TOKEN_ID, col_mint, pda_auth);
    let debt_vault = create_token_account(&mut svm, &payer, SPL_TOKEN_2022_ID, debt_mint, pda_auth);
    let bor_col = create_token_account(&mut svm, &payer, SPL_TOKEN_ID, col_mint, borrower.pubkey());
    let bor_debt = create_token_account(&mut svm, &payer, SPL_TOKEN_2022_ID, debt_mint, borrower.pubkey());
    let liq_col = create_token_account(&mut svm, &payer, SPL_TOKEN_ID, col_mint, liquidator.pubkey());
    let liq_debt = create_token_account(&mut svm, &payer, SPL_TOKEN_2022_ID, debt_mint, liquidator.pubkey());

    mint_tokens(&mut svm, &payer, SPL_TOKEN_ID, col_mint, bor_col, &payer, 1_000_000);
    mint_tokens(&mut svm, &payer, SPL_TOKEN_2022_ID, debt_mint, debt_vault, &payer, 5_000_000);
    mint_tokens(&mut svm, &payer, SPL_TOKEN_2022_ID, debt_mint, liq_debt, &payer, 1_000_000);

    // 1. InitMarket: maxLTV = 7500 (75%), liqBonus = 500 (5%), rate = 1_000_000/slot (0.1%/slot for fast test), price = 2_000_000 (2.0 debt/col)
    let mut init_data = vec![0u8, bump, 6, 6];
    init_data.extend_from_slice(&7500u16.to_le_bytes());
    init_data.extend_from_slice(&500u16.to_le_bytes());
    init_data.extend_from_slice(&1_000_000u64.to_le_bytes()); // 0.1% per slot
    init_data.extend_from_slice(&2_000_000u64.to_le_bytes()); // price = 2.0
    let m_init = send_ix(&mut svm, &payer, &[], Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(market_addr, false),
            AccountMeta::new_readonly(col_vault, false),
            AccountMeta::new_readonly(debt_vault, false),
        ],
        data: init_data,
    }).expect("Lending InitMarket failed");

    // 2. Deposit 100_000 collateral (value = 200_000 debt, max borrow @ 75% LTV = 150_000)
    let mut dep_data = vec![1u8];
    dep_data.extend_from_slice(&100_000u64.to_le_bytes());
    let m_dep = send_ix(&mut svm, &payer, &[&borrower], Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new_readonly(borrower.pubkey(), true),
            AccountMeta::new(market_addr, false),
            AccountMeta::new(obl_addr, false),
            AccountMeta::new_readonly(col_mint, false),
            AccountMeta::new(col_vault, false),
            AccountMeta::new(bor_col, false),
            AccountMeta::new_readonly(SPL_TOKEN_ID, false),
        ],
        data: dep_data,
    }).expect("Lending Deposit failed");

    // 3. Over-borrow (160_000 > 150_000 max LTV) MUST FAIL!
    let mut bad_bor = vec![2u8];
    bad_bor.extend_from_slice(&160_000u64.to_le_bytes());
    assert!(send_ix(&mut svm, &payer, &[&borrower], Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new_readonly(borrower.pubkey(), true),
            AccountMeta::new(market_addr, false),
            AccountMeta::new_readonly(pda_auth, false),
            AccountMeta::new(obl_addr, false),
            AccountMeta::new_readonly(debt_mint, false),
            AccountMeta::new(debt_vault, false),
            AccountMeta::new(bor_debt, false),
            AccountMeta::new_readonly(SPL_TOKEN_2022_ID, false),
        ],
        data: bad_bor,
    }).is_err(), "borrow exceeding max LTV must be rejected");

    // 4. Valid Borrow 140_000 Token-2022 debt
    let mut bor_data = vec![2u8];
    bor_data.extend_from_slice(&140_000u64.to_le_bytes());
    let m_bor = send_ix(&mut svm, &payer, &[&borrower], Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new_readonly(borrower.pubkey(), true),
            AccountMeta::new(market_addr, false),
            AccountMeta::new_readonly(pda_auth, false),
            AccountMeta::new(obl_addr, false),
            AccountMeta::new_readonly(debt_mint, false),
            AccountMeta::new(debt_vault, false),
            AccountMeta::new(bor_debt, false),
            AccountMeta::new_readonly(SPL_TOKEN_2022_ID, false),
        ],
        data: bor_data,
    }).expect("Lending Borrow failed");
    assert_eq!(token_balance(&svm, &bor_debt), 140_000);

    // 5. Advance Clock by 100 slots -> +10% interest -> debt accrues to 154_000 (> 150_000 max LTV -> liquidatable!)
    clk.slot = 1100;
    svm.set_sysvar::<Clock>(&clk);
    let mut liq_data = vec![4u8];
    liq_data.extend_from_slice(&50_000u64.to_le_bytes());
    let m_liq = send_ix(&mut svm, &payer, &[&liquidator], Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new_readonly(liquidator.pubkey(), true),
            AccountMeta::new(market_addr, false),
            AccountMeta::new_readonly(pda_auth, false),
            AccountMeta::new(obl_addr, false),
            AccountMeta::new_readonly(debt_mint, false),
            AccountMeta::new_readonly(col_mint, false),
            AccountMeta::new(debt_vault, false),
            AccountMeta::new(col_vault, false),
            AccountMeta::new(liq_debt, false),
            AccountMeta::new(liq_col, false),
            AccountMeta::new_readonly(SPL_TOKEN_2022_ID, false),
            AccountMeta::new_readonly(SPL_TOKEN_ID, false),
        ],
        data: liq_data,
    }).expect("Lending Liquidate failed");
    // 50_000 debt * 1.05 bonus / 2.0 price = 26_250 collateral seized!
    assert_eq!(token_balance(&svm, &liq_col), 26_250);

    // 6. Repay remaining 104_000 debt
    let mut rep_data = vec![3u8];
    rep_data.extend_from_slice(&104_000u64.to_le_bytes());
    let m_rep = send_ix(&mut svm, &payer, &[&borrower], Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new_readonly(borrower.pubkey(), true),
            AccountMeta::new(market_addr, false),
            AccountMeta::new(obl_addr, false),
            AccountMeta::new_readonly(debt_mint, false),
            AccountMeta::new(debt_vault, false),
            AccountMeta::new(bor_debt, false),
            AccountMeta::new_readonly(SPL_TOKEN_2022_ID, false),
        ],
        data: rep_data,
    }).expect("Lending Repay failed");
    assert_eq!(u64::from_le_bytes(svm.get_account(&obl_addr).unwrap().data[40..48].try_into().unwrap()), 0);

    println!(
        "[PASS] Lending      | .so = {:>6} B | CUs: init={}, dep={}, bor={}, liq={}, rep={}",
        so.len(),
        m_init.compute_units_consumed,
        m_dep.compute_units_consumed,
        m_bor.compute_units_consumed,
        m_liq.compute_units_consumed,
        m_rep.compute_units_consumed
    );
}

/// Test NFT Dutch Auction (Token-2022 1-of-1 NFT + Clock linear decay + System SOL CPI)!
fn test_dutch_auction() {
    let so = load_so("dutch_auction.so");
    let mut svm = LiteSVM::new();
    let payer = Keypair::new();
    let seller = Keypair::new();
    let buyer = Keypair::new();
    let program_id = Address::new_unique();
    svm.add_program(program_id, &so).expect("failed to load dutch_auction.so");
    svm.airdrop(&payer.pubkey(), 5_000_000_000).unwrap();
    svm.airdrop(&seller.pubkey(), 1_000_000_000).unwrap();
    svm.airdrop(&buyer.pubkey(), 5_000_000_000).unwrap();

    let auction_addr = Address::new_unique();
    let (pda_auth, bump) = Address::find_program_address(&[b"auct", auction_addr.as_ref()], &program_id);
    svm.set_account(auction_addr, Account {
        lamports: 10_000_000, data: vec![0u8; 144], owner: program_id, ..Default::default()
    }).unwrap();

    // Create 1-of-1 Token-2022 NFT (decimals = 0, supply = 1)
    let nft_mint = create_mint(&mut svm, &payer, SPL_TOKEN_2022_ID, payer.pubkey(), 0);
    let seller_nft = create_token_account(&mut svm, &payer, SPL_TOKEN_2022_ID, nft_mint, seller.pubkey());
    let escrow_nft = create_token_account(&mut svm, &payer, SPL_TOKEN_2022_ID, nft_mint, pda_auth);
    let buyer_nft = create_token_account(&mut svm, &payer, SPL_TOKEN_2022_ID, nft_mint, buyer.pubkey());
    mint_tokens(&mut svm, &payer, SPL_TOKEN_2022_ID, nft_mint, seller_nft, &payer, 1);

    // 1. CreateAuction: startPrice = 1_000_000_000 (1 SOL), reservePrice = 200_000_000 (0.2 SOL), slots [100, 500]
    let mut create_data = vec![0u8, bump, 0];
    create_data.extend_from_slice(&1_000_000_000u64.to_le_bytes());
    create_data.extend_from_slice(&200_000_000u64.to_le_bytes());
    create_data.extend_from_slice(&100u64.to_le_bytes());
    create_data.extend_from_slice(&500u64.to_le_bytes());
    let m_create = send_ix(&mut svm, &payer, &[&seller], Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new_readonly(seller.pubkey(), true),
            AccountMeta::new(auction_addr, false),
            AccountMeta::new_readonly(nft_mint, false),
            AccountMeta::new(seller_nft, false),
            AccountMeta::new(escrow_nft, false),
            AccountMeta::new_readonly(SPL_TOKEN_2022_ID, false),
        ],
        data: create_data,
    }).expect("Auction Create failed");
    assert_eq!(token_balance(&svm, &escrow_nft), 1);

    // 2. Advance Clock to slot 300 (exact midpoint of [100, 500] -> price = 600_000_000 lamports!)
    let mut clk = svm.get_sysvar::<Clock>();
    clk.slot = 300;
    svm.set_sysvar::<Clock>(&clk);

    let seller_before = svm.get_account(&seller.pubkey()).unwrap().lamports;
    let mut buy_data = vec![1u8];
    buy_data.extend_from_slice(&650_000_000u64.to_le_bytes()); // maxPrice >= 600M
    let m_buy = send_ix(&mut svm, &payer, &[&buyer], Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(buyer.pubkey(), true),
            AccountMeta::new(seller.pubkey(), false),
            AccountMeta::new(auction_addr, false),
            AccountMeta::new_readonly(pda_auth, false),
            AccountMeta::new_readonly(nft_mint, false),
            AccountMeta::new(escrow_nft, false),
            AccountMeta::new(buyer_nft, false),
            AccountMeta::new_readonly(SPL_TOKEN_2022_ID, false),
            AccountMeta::new_readonly(SYSTEM_PROGRAM_ID, false),
        ],
        data: buy_data,
    }).expect("Auction BuyNow failed");

    assert_eq!(token_balance(&svm, &buyer_nft), 1, "buyer must receive NFT");
    assert_eq!(token_balance(&svm, &escrow_nft), 0);
    assert_eq!(svm.get_account(&seller.pubkey()).unwrap().lamports - seller_before, 600_000_000);
    let settled = u64::from_le_bytes(svm.get_account(&auction_addr).unwrap().data[136..144].try_into().unwrap());
    assert_eq!(settled, 600_000_000);

    println!(
        "[PASS] DutchAuction | .so = {:>6} B | CUs: create={}, buyNow={}",
        so.len(), m_create.compute_units_consumed, m_buy.compute_units_consumed
    );
}

/// Test Bonding Curve Token Mint (Token-2022 MintTo + Burn + Zero-CPI SOL refund)!
fn test_bonding_curve() {
    let so = load_so("bonding_curve.so");
    let mut svm = LiteSVM::new();
    let payer = Keypair::new();
    let trader = Keypair::new();
    let program_id = Address::new_unique();
    svm.add_program(program_id, &so).expect("failed to load bonding_curve.so");
    svm.airdrop(&payer.pubkey(), 5_000_000_000).unwrap();
    svm.airdrop(&trader.pubkey(), 5_000_000_000).unwrap();

    let curve_addr = Address::new_unique();
    let (pda_auth, bump) = Address::find_program_address(&[b"curv", curve_addr.as_ref()], &program_id);
    svm.set_account(curve_addr, Account {
        lamports: 10_000_000, data: vec![0u8; 96], owner: program_id, ..Default::default()
    }).unwrap();

    // Token-2022 mint whose mint_authority IS the bonding curve PDA!
    let mint = create_mint(&mut svm, &payer, SPL_TOKEN_2022_ID, pda_auth, 6);
    let trader_ata = create_token_account(&mut svm, &payer, SPL_TOKEN_2022_ID, mint, trader.pubkey());

    // 1. InitCurve: vSol = 30 SOL, vTok = 1_000_000_000_000, maxSupply = 800_000_000_000, fee = 100 bps (1%)
    let mut init_data = vec![0u8, bump, 6];
    init_data.extend_from_slice(&30_000_000_000u64.to_le_bytes());
    init_data.extend_from_slice(&1_000_000_000_000u64.to_le_bytes());
    init_data.extend_from_slice(&800_000_000_000u64.to_le_bytes());
    init_data.extend_from_slice(&100u64.to_le_bytes());
    let m_init = send_ix(&mut svm, &payer, &[], Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(curve_addr, false),
            AccountMeta::new_readonly(mint, false),
        ],
        data: init_data,
    }).expect("Curve Init failed");

    // 2. Buy with 1_000_000_000 lamports (1 SOL -> 1% fee = 10M, net = 990M)
    // Expected tokensOut = 990_000_000 * 1_000_000_000_000 / 30_990_000_000 = 31_945_788_964 (uses 128-bit mulDiv64!)
    let mut buy_data = vec![1u8];
    buy_data.extend_from_slice(&1_000_000_000u64.to_le_bytes());
    buy_data.extend_from_slice(&30_000_000_000u64.to_le_bytes());
    let m_buy = send_ix(&mut svm, &payer, &[&trader], Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(trader.pubkey(), true),
            AccountMeta::new(curve_addr, false),
            AccountMeta::new_readonly(pda_auth, false),
            AccountMeta::new(mint, false),
            AccountMeta::new(trader_ata, false),
            AccountMeta::new_readonly(SPL_TOKEN_2022_ID, false),
            AccountMeta::new_readonly(SYSTEM_PROGRAM_ID, false),
        ],
        data: buy_data,
    }).expect("Curve Buy failed");
    let bought = token_balance(&svm, &trader_ata);
    assert_eq!(bought, 31_945_788_964, "exact 128-bit bonding curve mint amount mismatch");

    // 3. Sell half the tokens back (burns Token-2022 + zero-CPI direct lamport payout!)
    let sell_amt = bought / 2;
    let trader_sol_before = svm.get_account(&trader.pubkey()).unwrap().lamports;
    let mut sell_data = vec![2u8];
    sell_data.extend_from_slice(&sell_amt.to_le_bytes());
    sell_data.extend_from_slice(&400_000_000u64.to_le_bytes());
    let m_sell = send_ix(&mut svm, &payer, &[&trader], Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(trader.pubkey(), true),
            AccountMeta::new(curve_addr, false),
            AccountMeta::new(mint, false),
            AccountMeta::new(trader_ata, false),
            AccountMeta::new_readonly(SPL_TOKEN_2022_ID, false),
        ],
        data: sell_data,
    }).expect("Curve Sell failed");
    let sol_received = svm.get_account(&trader.pubkey()).unwrap().lamports - trader_sol_before;
    assert!(sol_received > 480_000_000 && sol_received < 510_000_000, "unexpected sol refund: {sol_received}");
    assert_eq!(token_balance(&svm, &trader_ata), bought - sell_amt);

    println!(
        "[PASS] BondingCurve | .so = {:>6} B | CUs: init={}, buy={}, sell={}",
        so.len(),
        m_init.compute_units_consumed,
        m_buy.compute_units_consumed,
        m_sell.compute_units_consumed
    );
}

/// Run a program that reads a seed from account data[0..8] and writes its result to data[8..16].
fn run_seed(so: &[u8], seed: u64) -> u64 {
    let mut svm = LiteSVM::new();
    let payer = Keypair::new();
    let program_id = Address::new_unique();
    svm.add_program(program_id, so).unwrap();
    svm.airdrop(&payer.pubkey(), 1_000_000_000).unwrap();

    let acc_addr = Address::new_unique();
    let mut data = vec![0u8; 16];
    data[0..8].copy_from_slice(&seed.to_le_bytes());
    svm.set_account(acc_addr, Account {
        lamports: 1_000_000, data, owner: program_id, ..Default::default()
    }).unwrap();

    let ix = Instruction {
        program_id, accounts: vec![AccountMeta::new(acc_addr, false)], data: vec![0u8],
    };
    send_ix(&mut svm, &payer, &[], ix).expect("scalar semantics program failed");
    let after = svm.get_account(&acc_addr).unwrap();
    u64::from_le_bytes(after.data[8..16].try_into().unwrap())
}

/// Scalar ops where Lean is total but raw sBPF is not: `Nat.sub` saturates at 0 and
/// `x / 0`, `x % 0` are defined (`0` and `x`). Both used to diverge from the Lean model.
fn test_scalar_semantics() {
    let natsub = load_so("natsub.so");
    let divzero = load_so("divzero.so");

    for (seed, expected) in [(0u64, 0u64), (1, 0), (5, 4), (u64::MAX, u64::MAX - 1)] {
        let got = run_seed(&natsub, seed);
        assert_eq!(got, expected, "(Nat {seed}) - 1 must saturate at 0, got {got:#x}");
    }

    // Example: q = 1000 / d, r = 1000 % d, result = q ^^^ r
    for (seed, expected) in [(0u64, 1000u64), (1, 1000), (7, 142 ^ 6)] {
        let got = run_seed(&divzero, seed);
        assert_eq!(got, expected, "1000 / {seed} ^^^ 1000 % {seed}, got {got:#x}");
    }

    println!("[PASS] ScalarSemantics | Nat.sub saturates at 0, x / 0 = 0, x % 0 = x");
}

fn bench_vs_rust() {
    println!("\n==================================================================================");
    println!("  HEAD-TO-HEAD BENCHMARK: LeanSVM (Lean 4) vs Hand-Rolled `#![no_std]` Rust (LLVM 22 -O3)");
    println!("==================================================================================");

    // 1. Noop
    let lean_noop = load_so("noop.so");
    let rust_noop = load_so("rust/rust_noop.so");
    let run_noop = |so: &[u8]| -> u64 {
        let mut svm = LiteSVM::new();
        let payer = Keypair::new();
        let pid = Address::new_unique();
        svm.add_program(pid, so).unwrap();
        svm.airdrop(&payer.pubkey(), 1_000_000_000).unwrap();
        send_ix(&mut svm, &payer, &[], Instruction { program_id: pid, accounts: vec![], data: vec![] })
            .unwrap()
            .compute_units_consumed
    };
    let (ln_cu, rn_cu) = (run_noop(&lean_noop), run_noop(&rust_noop));
    println!(
        "  Noop         | Lean: {:>5} B, {:>4} CU | Rust: {:>5} B, {:>4} CU | Size: {:.2}x",
        lean_noop.len(), ln_cu, rust_noop.len(), rn_cu,
        rust_noop.len() as f64 / lean_noop.len() as f64
    );

    // 2. Counter (init, inc, add)
    let lean_cnt = load_so("counter.so");
    let rust_cnt = load_so("rust/rust_counter.so");
    let run_cnt = |so: &[u8]| -> (u64, u64, u64) {
        let mut svm = LiteSVM::new();
        let payer = Keypair::new();
        let acc = Address::new_unique();
        let pid = Address::new_unique();
        svm.add_program(pid, so).unwrap();
        svm.airdrop(&payer.pubkey(), 1_000_000_000).unwrap();
        svm.set_account(acc, Account { lamports: 1_000_000, data: vec![0u8; 8], owner: pid, ..Default::default() }).unwrap();
        let c0 = send_ix(&mut svm, &payer, &[], Instruction { program_id: pid, accounts: vec![AccountMeta::new(acc, false)], data: vec![0u8] }).unwrap().compute_units_consumed;
        let c1 = send_ix(&mut svm, &payer, &[], Instruction { program_id: pid, accounts: vec![AccountMeta::new(acc, false)], data: vec![1u8] }).unwrap().compute_units_consumed;
        let mut ad = vec![2u8]; ad.extend_from_slice(&41u64.to_le_bytes());
        let c2 = send_ix(&mut svm, &payer, &[], Instruction { program_id: pid, accounts: vec![AccountMeta::new(acc, false)], data: ad }).unwrap().compute_units_consumed;
        assert_eq!(u64::from_le_bytes(svm.get_account(&acc).unwrap().data[0..8].try_into().unwrap()), 42);
        (c0, c1, c2)
    };
    let (lc0, lc1, lc2) = run_cnt(&lean_cnt);
    let (rc0, rc1, rc2) = run_cnt(&rust_cnt);
    println!(
        "  Counter      | Lean: {:>5} B, {}/{}/{} CU | Rust: {:>5} B, {}/{}/{} CU | Size: {:.2}x",
        lean_cnt.len(), lc0, lc1, lc2, rust_cnt.len(), rc0, rc1, rc2,
        rust_cnt.len() as f64 / lean_cnt.len() as f64
    );

    // 3. Vault (3 accounts + 32B pubkey eq + lamport transfer + sol_log_)
    let lean_vlt = load_so("vault.so");
    let rust_vlt = load_so("rust/rust_vault.so");
    let run_vlt = |so: &[u8]| -> u64 {
        let mut svm = LiteSVM::new();
        let payer = Keypair::new();
        let auth = Keypair::new();
        let vlt = Address::new_unique();
        let dst = Address::new_unique();
        let pid = Address::new_unique();
        svm.add_program(pid, so).unwrap();
        svm.airdrop(&payer.pubkey(), 1_000_000_000).unwrap();
        svm.set_account(vlt, Account { lamports: 10_000_000, data: auth.pubkey().to_bytes().to_vec(), owner: pid, ..Default::default() }).unwrap();
        svm.set_account(dst, Account { lamports: 2_000_000, data: vec![], owner: SYSTEM_PROGRAM_ID, ..Default::default() }).unwrap();
        let cu = send_ix(&mut svm, &payer, &[&auth], Instruction {
            program_id: pid,
            accounts: vec![
                AccountMeta::new_readonly(auth.pubkey(), true),
                AccountMeta::new(vlt, false),
                AccountMeta::new(dst, false),
            ],
            data: 3_500_000u64.to_le_bytes().to_vec(),
        }).unwrap().compute_units_consumed;
        assert_eq!(svm.get_account(&dst).unwrap().lamports, 5_500_000);
        cu
    };
    let (lv_cu, rv_cu) = (run_vlt(&lean_vlt), run_vlt(&rust_vlt));
    println!(
        "  Vault        | Lean: {:>5} B, {:>4} CU | Rust: {:>5} B, {:>4} CU | Size: {:.2}x",
        lean_vlt.len(), lv_cu, rust_vlt.len(), rv_cu,
        rust_vlt.len() as f64 / lean_vlt.len() as f64
    );

    // 4. DutchAuction (Token-2022 NFT + Clock + System CPI + PDA CPI)
    let lean_auc = load_so("dutch_auction.so");
    let rust_auc = load_so("rust/rust_dutch_auction.so");
    let run_auc = |so: &[u8]| -> (u64, u64) {
        let mut svm = LiteSVM::new();
        let payer = Keypair::new();
        let seller = Keypair::new();
        let buyer = Keypair::new();
        let pid = Address::new_unique();
        svm.add_program(pid, so).unwrap();
        svm.airdrop(&payer.pubkey(), 5_000_000_000).unwrap();
        svm.airdrop(&seller.pubkey(), 1_000_000_000).unwrap();
        svm.airdrop(&buyer.pubkey(), 5_000_000_000).unwrap();
        let auction = Address::new_unique();
        let (pda, bump) = Address::find_program_address(&[b"auct", auction.as_ref()], &pid);
        svm.set_account(auction, Account { lamports: 10_000_000, data: vec![0u8; 144], owner: pid, ..Default::default() }).unwrap();
        let mint = create_mint(&mut svm, &payer, SPL_TOKEN_2022_ID, payer.pubkey(), 0);
        let s_nft = create_token_account(&mut svm, &payer, SPL_TOKEN_2022_ID, mint, seller.pubkey());
        let e_nft = create_token_account(&mut svm, &payer, SPL_TOKEN_2022_ID, mint, pda);
        let b_nft = create_token_account(&mut svm, &payer, SPL_TOKEN_2022_ID, mint, buyer.pubkey());
        mint_tokens(&mut svm, &payer, SPL_TOKEN_2022_ID, mint, s_nft, &payer, 1);
        let mut cd = vec![0u8, bump, 0];
        cd.extend_from_slice(&1_000_000_000u64.to_le_bytes());
        cd.extend_from_slice(&200_000_000u64.to_le_bytes());
        cd.extend_from_slice(&100u64.to_le_bytes());
        cd.extend_from_slice(&500u64.to_le_bytes());
        let c_create = send_ix(&mut svm, &payer, &[&seller], Instruction {
            program_id: pid,
            accounts: vec![
                AccountMeta::new_readonly(seller.pubkey(), true),
                AccountMeta::new(auction, false),
                AccountMeta::new_readonly(mint, false),
                AccountMeta::new(s_nft, false),
                AccountMeta::new(e_nft, false),
                AccountMeta::new_readonly(SPL_TOKEN_2022_ID, false),
            ],
            data: cd,
        }).unwrap().compute_units_consumed;
        let mut clk = svm.get_sysvar::<Clock>(); clk.slot = 300; svm.set_sysvar::<Clock>(&clk);
        let mut bd = vec![1u8]; bd.extend_from_slice(&650_000_000u64.to_le_bytes());
        let c_buy = send_ix(&mut svm, &payer, &[&buyer], Instruction {
            program_id: pid,
            accounts: vec![
                AccountMeta::new(buyer.pubkey(), true),
                AccountMeta::new(seller.pubkey(), false),
                AccountMeta::new(auction, false),
                AccountMeta::new_readonly(pda, false),
                AccountMeta::new_readonly(mint, false),
                AccountMeta::new(e_nft, false),
                AccountMeta::new(b_nft, false),
                AccountMeta::new_readonly(SPL_TOKEN_2022_ID, false),
                AccountMeta::new_readonly(SYSTEM_PROGRAM_ID, false),
            ],
            data: bd,
        }).unwrap().compute_units_consumed;
        assert_eq!(token_balance(&svm, &b_nft), 1);
        (c_create, c_buy)
    };
    let (la0, la1) = run_auc(&lean_auc);
    let (ra0, ra1) = run_auc(&rust_auc);
    println!(
        "  DutchAuction | Lean: {:>5} B, {}/{} CU | Rust: {:>5} B, {}/{} CU | Size: {:.2}x",
        lean_auc.len(), la0, la1, rust_auc.len(), ra0, ra1,
        rust_auc.len() as f64 / lean_auc.len() as f64
    );
    println!("==================================================================================");
}

fn main() {
    println!("==================================================================================");
    println!("  lean-svm Full LiteSVM Verification & CU Benchmarks (SPL Token + Token-2022)");
    println!("==================================================================================");
    test_noop();
    test_counter();
    test_vault();
    test_hashcheck();
    test_amm();
    test_lending();
    test_dutch_auction();
    test_bonding_curve();
    test_scalar_semantics();
    bench_vs_rust();
    println!("  ALL 10 LEAN 4 PROGRAMS + HEAD-TO-HEAD RUST BENCHMARKS PASSED!");
    println!("==================================================================================");
}
