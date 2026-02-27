//! E2E Benchmark Codebase (~1000 lines)
//!
//! A realistic banking/accounting system for formal verification performance testing.
//! Contains ~40-50 functions with contracts to measure incremental verification performance.
//!
//! This crate is NOT a workspace member - it's a standalone test fixture used by
//! the E2E performance tests in `crates/driver/tests/e2e_performance.rs`.




// ============================================================================
// PART A: DATA STRUCTURES (200-250 lines)
// ============================================================================

/// Unique account identifier
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AccountId(u64);

impl AccountId {
    #[doc = "rust_fv::requires::id > 0"]
    pub fn new(id: u64) -> Self {
        AccountId(id)
    }

    #[doc = "rust_fv::pure"]
    #[doc = "rust_fv::ensures::result > 0"]
    pub fn value(&self) -> u64 {
        self.0
    }
}

/// Account type classification
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccountType {
    Checking,
    Savings,
    Investment,
}

impl AccountType {
    #[doc = "rust_fv::pure"]
    pub fn is_liquid(&self) -> bool {
        match self {
            AccountType::Checking => true,
            AccountType::Savings => true,
            AccountType::Investment => false,
        }
    }

    #[doc = "rust_fv::pure"]
    pub fn interest_rate(&self) -> u32 {
        match self {
            AccountType::Checking => 0,
            AccountType::Savings => 2,
            AccountType::Investment => 5,
        }
    }
}

/// Account balance in cents (to avoid floating point issues)
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Balance(i64);

impl Balance {
    #[doc = "rust_fv::requires::cents >= 0"]
    pub fn new(cents: i64) -> Self {
        Balance(cents)
    }

    #[doc = "rust_fv::pure"]
    #[doc = "rust_fv::ensures::result >= 0"]
    pub fn cents(&self) -> i64 {
        self.0
    }

    pub fn zero() -> Self {
        Balance(0)
    }

    pub fn add(&self, other: Balance) -> Balance {
        Balance(self.0 + other.0)
    }

    pub fn subtract(&self, other: Balance) -> Balance {
        Balance(self.0 - other.0)
    }
}

/// Bank account with balance and metadata
#[derive(Debug, Clone)]
pub struct Account {
    pub id: AccountId,
    pub account_type: AccountType,
    pub balance: Balance,
    pub is_active: bool,
}

impl Account {
    pub fn new(id: AccountId, account_type: AccountType, initial_balance: Balance) -> Self {
        Account {
            id,
            account_type,
            balance: initial_balance,
            is_active: true,
        }
    }

    #[doc = "rust_fv::pure"]
    pub fn is_empty(&self) -> bool {
        self.balance.0 == 0
    }

    #[doc = "rust_fv::pure"]
    pub fn can_withdraw(&self, amount: Balance) -> bool {
        self.balance.0 >= amount.0 && amount.0 > 0
    }

    #[doc = "rust_fv::pure"]
    pub fn is_overdrawn(&self) -> bool {
        self.balance.0 < 0
    }
}

/// Transaction type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransactionType {
    Deposit,
    Withdrawal,
    Transfer,
    Interest,
}

impl TransactionType {
    #[doc = "rust_fv::pure"]
    pub fn requires_destination(&self) -> bool {
        matches!(self, TransactionType::Transfer)
    }

    #[doc = "rust_fv::pure"]
    pub fn affects_balance(&self) -> bool {
        true
    }
}

/// Transaction record
#[derive(Debug, Clone)]
pub struct Transaction {
    pub transaction_type: TransactionType,
    pub source: AccountId,
    pub destination: Option<AccountId>,
    pub amount: Balance,
    pub timestamp: u64,
}

impl Transaction {
    pub fn deposit(source: AccountId, amount: Balance, timestamp: u64) -> Self {
        Transaction {
            transaction_type: TransactionType::Deposit,
            source,
            destination: None,
            amount,
            timestamp,
        }
    }

    pub fn withdrawal(source: AccountId, amount: Balance, timestamp: u64) -> Self {
        Transaction {
            transaction_type: TransactionType::Withdrawal,
            source,
            destination: None,
            amount,
            timestamp,
        }
    }

    pub fn transfer(source: AccountId, dest: AccountId, amount: Balance, timestamp: u64) -> Self {
        Transaction {
            transaction_type: TransactionType::Transfer,
            source,
            destination: Some(dest),
            amount,
            timestamp,
        }
    }

    #[doc = "rust_fv::pure"]
    pub fn is_valid(&self) -> bool {
        if self.transaction_type == TransactionType::Transfer {
            self.destination.is_some()
        } else {
            true
        }
    }
}

/// Ledger entry
#[derive(Debug, Clone)]
pub struct LedgerEntry {
    pub account: AccountId,
    pub balance_before: Balance,
    pub balance_after: Balance,
    pub transaction: Transaction,
}

impl LedgerEntry {
    pub fn new(
        account: AccountId,
        balance_before: Balance,
        balance_after: Balance,
        transaction: Transaction,
    ) -> Self {
        LedgerEntry {
            account,
            balance_before,
            balance_after,
            transaction,
        }
    }

    #[doc = "rust_fv::pure"]
    pub fn balance_change(&self) -> i64 {
        self.balance_after.0 - self.balance_before.0
    }
}

/// Simple ledger (audit log)
#[derive(Debug, Clone)]
pub struct Ledger {
    entries: Vec<LedgerEntry>,
}

impl Ledger {
    pub fn new() -> Self {
        Ledger {
            entries: Vec::new(),
        }
    }

    #[doc = "rust_fv::pure"]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    #[doc = "rust_fv::pure"]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn add_entry(&mut self, entry: LedgerEntry) {
        self.entries.push(entry);
    }

    pub fn get_entry(&self, idx: usize) -> &LedgerEntry {
        &self.entries[idx]
    }
}

impl Default for Ledger {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// PART B: BUSINESS LOGIC FUNCTIONS (300-350 lines)
// ============================================================================

/// Validate account ID is non-zero
#[doc = "rust_fv::pure"]
pub fn validate_account_id(id: AccountId) -> bool {
    id.0 > 0
}

/// Validate balance is non-negative
#[doc = "rust_fv::pure"]
pub fn validate_balance(balance: Balance) -> bool {
    balance.0 >= 0
}

/// Validate amount is positive
#[doc = "rust_fv::pure"]
pub fn validate_amount(amount: Balance) -> bool {
    amount.0 > 0
}

/// Check if account has sufficient funds
#[doc = "rust_fv::pure"]
pub fn has_sufficient_funds(account: &Account, amount: Balance) -> bool {
    account.balance.0 >= amount.0
}

/// Check if account is active
#[doc = "rust_fv::pure"]
pub fn is_account_active(account: &Account) -> bool {
    account.is_active
}

/// Validate account is ready for transaction
#[doc = "rust_fv::pure"]
pub fn validate_account_for_transaction(account: &Account) -> bool {
    account.is_active && account.balance.0 >= 0 && account.id.0 > 0
}

/// Deposit money into an account
pub fn deposit(account: &mut Account, amount: Balance) {
    account.balance = account.balance.add(amount);
}

/// Withdraw money from an account
pub fn withdraw(account: &mut Account, amount: Balance) -> bool {
    if account.balance.0 >= amount.0 {
        account.balance = account.balance.subtract(amount);
        true
    } else {
        false
    }
}

/// Transfer money between accounts
pub fn transfer(from: &mut Account, to: &mut Account, amount: Balance) -> bool {
    if from.balance.0 >= amount.0 && from.id.0 != to.id.0 {
        withdraw(from, amount);
        deposit(to, amount);
        true
    } else {
        false
    }
}

/// Calculate interest for an account
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::requires::rate <= 100"]
pub fn calculate_interest(balance: Balance, rate: u32) -> Balance {
    let interest = (balance.0 * rate as i64) / 100;
    Balance(interest)
}

/// Apply interest to account
pub fn apply_interest(account: &mut Account) {
    let rate = account.account_type.interest_rate();
    let interest = calculate_interest(account.balance, rate);
    deposit(account, interest);
}

/// Close account (set inactive, balance must be zero)
pub fn close_account(account: &mut Account) -> bool {
    if account.balance.0 == 0 {
        account.is_active = false;
        true
    } else {
        false
    }
}

/// Reopen account
pub fn reopen_account(account: &mut Account) {
    account.is_active = true;
}

/// Validate transfer preconditions
#[doc = "rust_fv::pure"]
pub fn can_transfer(from: &Account, to: &Account, amount: Balance) -> bool {
    from.is_active
        && to.is_active
        && from.balance.0 >= amount.0
        && amount.0 > 0
        && from.id.0 != to.id.0
}

/// Get total balance across multiple accounts
#[doc = "rust_fv::requires::accounts.len() > 0"]
pub fn total_balance(accounts: &[Account]) -> Balance {
    let mut total = 0i64;
    for account in accounts {
        total += account.balance.0;
    }
    Balance(total)
}

/// Count active accounts
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::requires::accounts.len() > 0"]
#[doc = "rust_fv::ensures::result <= accounts.len()"]
pub fn count_active(accounts: &[Account]) -> usize {
    accounts.iter().filter(|a| a.is_active).count()
}

/// Count accounts by type
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::requires::accounts.len() > 0"]
#[doc = "rust_fv::ensures::result <= accounts.len()"]
pub fn count_by_type(accounts: &[Account], account_type: AccountType) -> usize {
    accounts
        .iter()
        .filter(|a| a.account_type == account_type)
        .count()
}

/// Find account by ID
#[doc = "rust_fv::requires::accounts.len() > 0"]
pub fn find_account(accounts: &[Account], id: AccountId) -> Option<&Account> {
    accounts.iter().find(|a| a.id == id)
}

/// Validate all accounts have positive balances
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::requires::accounts.len() > 0"]
pub fn all_balances_positive(accounts: &[Account]) -> bool {
    accounts.iter().all(|a| a.balance.0 >= 0)
}

/// Check if any account is overdrawn
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::requires::accounts.len() > 0"]
pub fn any_overdrawn(accounts: &[Account]) -> bool {
    accounts.iter().any(|a| a.balance.0 < 0)
}

/// Calculate total deposits in ledger
#[doc = "rust_fv::requires::ledger.len() > 0"]
pub fn total_deposits(ledger: &Ledger) -> Balance {
    let mut total = 0i64;
    for i in 0..ledger.len() {
        let entry = ledger.get_entry(i);
        if entry.transaction.transaction_type == TransactionType::Deposit {
            total += entry.transaction.amount.0;
        }
    }
    Balance(total)
}

/// Calculate total withdrawals in ledger
#[doc = "rust_fv::requires::ledger.len() > 0"]
pub fn total_withdrawals(ledger: &Ledger) -> Balance {
    let mut total = 0i64;
    for i in 0..ledger.len() {
        let entry = ledger.get_entry(i);
        if entry.transaction.transaction_type == TransactionType::Withdrawal {
            total += entry.transaction.amount.0;
        }
    }
    Balance(total)
}

/// Record transaction in ledger
pub fn record_transaction(
    ledger: &mut Ledger,
    account: &Account,
    balance_before: Balance,
    balance_after: Balance,
    transaction: Transaction,
) {
    let entry = LedgerEntry::new(account.id, balance_before, balance_after, transaction);
    ledger.add_entry(entry);
}

// ============================================================================
// PART C: UTILITY/HELPER FUNCTIONS (200-250 lines)
// ============================================================================

/// Clamp value to range [min, max]
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::requires::min <= max"]
#[doc = "rust_fv::ensures::result >= min && result <= max"]
pub fn clamp(value: i64, min: i64, max: i64) -> i64 {
    if value < min {
        min
    } else if value > max {
        max
    } else {
        value
    }
}

/// Absolute difference between two values
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::ensures::result >= 0"]
pub fn abs_diff(a: i64, b: i64) -> i64 {
    if a >= b {
        a - b
    } else {
        b - a
    }
}

/// Safe division (returns 0 if divisor is 0)
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::ensures::b != 0 ==> result == a / b"]
#[doc = "rust_fv::ensures::b == 0 ==> result == 0"]
pub fn safe_divide(a: i64, b: i64) -> i64 {
    if b != 0 {
        a / b
    } else {
        0
    }
}

/// Bounded addition (saturates at i64::MAX)
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::requires::a >= 0"]
#[doc = "rust_fv::requires::b >= 0"]
#[doc = "rust_fv::ensures::result >= a && result >= b"]
pub fn bounded_add(a: i64, b: i64) -> i64 {
    a.saturating_add(b)
}

/// Bounded subtraction (saturates at 0)
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::requires::a >= 0"]
#[doc = "rust_fv::requires::b >= 0"]
#[doc = "rust_fv::ensures::result >= 0"]
pub fn bounded_sub(a: i64, b: i64) -> i64 {
    if a >= b {
        a - b
    } else {
        0
    }
}

/// Bounded multiplication (saturates at i64::MAX)
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::requires::a >= 0"]
#[doc = "rust_fv::requires::b >= 0"]
#[doc = "rust_fv::ensures::result >= 0"]
pub fn bounded_mul(a: i64, b: i64) -> i64 {
    a.saturating_mul(b)
}

/// Check if value is in range [min, max]
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::requires::min <= max"]
pub fn in_range(value: i64, min: i64, max: i64) -> bool {
    value >= min && value <= max
}

/// Min of two values
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::ensures::result <= a && result <= b"]
#[doc = "rust_fv::ensures::result == a || result == b"]
pub fn min(a: i64, b: i64) -> i64 {
    if a <= b {
        a
    } else {
        b
    }
}

/// Max of two values
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::ensures::result >= a && result >= b"]
#[doc = "rust_fv::ensures::result == a || result == b"]
pub fn max(a: i64, b: i64) -> i64 {
    if a >= b {
        a
    } else {
        b
    }
}

/// Absolute value
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::ensures::result >= 0"]
#[doc = "rust_fv::ensures::(a >= 0 && result == a) || (a < 0 && result == -a)"]
pub fn abs(a: i64) -> i64 {
    if a >= 0 {
        a
    } else {
        -a
    }
}

/// Sign of value (-1, 0, or 1)
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::ensures::result >= -1 && result <= 1"]
pub fn sign(a: i64) -> i64 {
    if a > 0 {
        1
    } else if a < 0 {
        -1
    } else {
        0
    }
}

/// Is value even?
#[doc = "rust_fv::pure"]
pub fn is_even(a: i64) -> bool {
    a % 2 == 0
}

/// Is value odd?
#[doc = "rust_fv::pure"]
pub fn is_odd(a: i64) -> bool {
    a % 2 != 0
}

/// Convert cents to dollars (integer division)
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::requires::cents >= 0"]
#[doc = "rust_fv::ensures::result >= 0"]
pub fn cents_to_dollars(cents: i64) -> i64 {
    cents / 100
}

/// Convert dollars to cents
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::requires::dollars >= 0"]
#[doc = "rust_fv::ensures::result >= 0"]
#[doc = "rust_fv::ensures::result == dollars * 100"]
pub fn dollars_to_cents(dollars: i64) -> i64 {
    dollars * 100
}

/// Round cents to nearest dollar
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::requires::cents >= 0"]
#[doc = "rust_fv::ensures::result >= 0"]
pub fn round_to_dollars(cents: i64) -> i64 {
    (cents + 50) / 100
}

// ============================================================================
// PART D: COMPLEX FUNCTIONS (200-250 lines)
// ============================================================================

/// Process multiple deposits in batch
#[doc = "rust_fv::requires::amounts.len() > 0"]
pub fn batch_deposit(account: &mut Account, amounts: &[Balance]) -> usize {
    let mut count = 0;
    for amount in amounts {
        if amount.0 > 0 {
            deposit(account, *amount);
            count += 1;
        }
    }
    count
}

/// Process multiple withdrawals in batch
#[doc = "rust_fv::requires::amounts.len() > 0"]
pub fn batch_withdraw(account: &mut Account, amounts: &[Balance]) -> usize {
    let mut count = 0;
    for amount in amounts {
        if amount.0 > 0 && account.balance.0 >= amount.0 {
            withdraw(account, *amount);
            count += 1;
        }
    }
    count
}

/// Distribute amount evenly across accounts
#[doc = "rust_fv::requires::accounts.len() > 0"]
pub fn distribute_evenly(accounts: &mut [Account], total_amount: Balance) {
    let per_account = total_amount.0 / accounts.len() as i64;
    let amount = Balance(per_account);

    for account in accounts.iter_mut() {
        if account.is_active && per_account > 0 {
            deposit(account, amount);
        }
    }
}

/// Sweep small balances to a target account
#[doc = "rust_fv::requires::accounts.len() > 0"]
#[doc = "rust_fv::requires::target.is_active"]
pub fn sweep_small_balances(accounts: &mut [Account], target: &mut Account, threshold: Balance) {
    for account in accounts.iter_mut() {
        if account.is_active
            && account.balance.0 > 0
            && account.balance.0 < threshold.0
            && account.id.0 != target.id.0
        {
            let amount = account.balance;
            if withdraw(account, amount) {
                deposit(target, amount);
            }
        }
    }
}

/// Calculate compound interest over multiple periods
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::requires::rate <= 100"]
#[doc = "rust_fv::requires::periods > 0"]
pub fn compound_interest(principal: Balance, rate: u32, periods: u32) -> Balance {
    let mut amount = principal.0;
    for _ in 0..periods {
        let interest = (amount * rate as i64) / 100;
        amount = bounded_add(amount, interest);
    }
    Balance(amount)
}

/// Apply compound interest to account
#[doc = "rust_fv::requires::periods > 0"]
pub fn apply_compound_interest(account: &mut Account, periods: u32) {
    let rate = account.account_type.interest_rate();
    let new_balance = compound_interest(account.balance, rate, periods);
    let interest = Balance(new_balance.0 - account.balance.0);
    deposit(account, interest);
}

/// Transfer with percentage fee
#[doc = "rust_fv::requires::fee_percent <= 100"]
pub fn transfer_with_fee(
    from: &mut Account,
    to: &mut Account,
    amount: Balance,
    fee_percent: u32,
) -> bool {
    let fee = (amount.0 * fee_percent as i64) / 100;
    let total = amount.0 + fee;

    if from.balance.0 >= total {
        let total_amount = Balance(total);
        withdraw(from, total_amount);
        deposit(to, amount);
        true
    } else {
        false
    }
}

/// Balance accounts to equal distribution
#[doc = "rust_fv::requires::accounts.len() >= 2"]
pub fn balance_accounts(accounts: &mut [Account]) {
    let total = total_balance(accounts);
    let target_balance = total.0 / accounts.len() as i64;

    for account in accounts.iter_mut() {
        if account.is_active {
            if account.balance.0 < target_balance {
                let diff = target_balance - account.balance.0;
                account.balance = Balance(account.balance.0 + diff);
            } else if account.balance.0 > target_balance {
                let diff = account.balance.0 - target_balance;
                account.balance = Balance(account.balance.0 - diff);
            }
        }
    }
}

/// Find account with maximum balance
#[doc = "rust_fv::requires::accounts.len() > 0"]
pub fn find_max_balance(accounts: &[Account]) -> Option<&Account> {
    let mut max_account: Option<&Account> = None;
    let mut max_balance = 0i64;

    for account in accounts {
        if account.balance.0 > max_balance {
            max_balance = account.balance.0;
            max_account = Some(account);
        }
    }

    max_account
}

/// Find account with minimum balance
#[doc = "rust_fv::requires::accounts.len() > 0"]
pub fn find_min_balance(accounts: &[Account]) -> Option<&Account> {
    let mut min_account: Option<&Account> = None;
    let mut min_balance = i64::MAX;

    for account in accounts {
        if account.balance.0 < min_balance {
            min_balance = account.balance.0;
            min_account = Some(account);
        }
    }

    min_account
}

/// Validate ledger consistency (all balances non-negative after each transaction)
#[doc = "rust_fv::requires::ledger.len() > 0"]
pub fn validate_ledger_consistency(ledger: &Ledger) -> bool {
    for i in 0..ledger.len() {
        let entry = ledger.get_entry(i);
        if entry.balance_after.0 < 0 {
            return false;
        }
    }
    true
}

/// Calculate net change for account from ledger
#[doc = "rust_fv::requires::ledger.len() > 0"]
pub fn calculate_net_change(ledger: &Ledger, account_id: AccountId) -> i64 {
    let mut net_change = 0i64;
    for i in 0..ledger.len() {
        let entry = ledger.get_entry(i);
        if entry.account == account_id {
            net_change += entry.balance_change();
        }
    }
    net_change
}

/// Apply percentage change to balance
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::requires::percent <= 100"]
pub fn apply_percentage(balance: Balance, percent: u32) -> Balance {
    let change = (balance.0 * percent as i64) / 100;
    Balance(bounded_add(balance.0, change))
}

/// Check if transaction is suspicious (amount > threshold)
#[doc = "rust_fv::pure"]
pub fn is_suspicious_transaction(transaction: &Transaction, threshold: Balance) -> bool {
    transaction.amount.0 > threshold.0
}

/// Calculate daily balance average
#[doc = "rust_fv::requires::balances.len() > 0"]
pub fn average_balance(balances: &[Balance]) -> Balance {
    let mut total = 0i64;
    for balance in balances {
        total += balance.0;
    }
    Balance(total / balances.len() as i64)
}

/// Count transactions by type in ledger
#[doc = "rust_fv::requires::ledger.len() > 0"]
#[doc = "rust_fv::ensures::result <= ledger.len()"]
pub fn count_transactions_by_type(ledger: &Ledger, transaction_type: TransactionType) -> usize {
    let mut count = 0;
    for i in 0..ledger.len() {
        let entry = ledger.get_entry(i);
        if entry.transaction.transaction_type == transaction_type {
            count += 1;
        }
    }
    count
}

// ============================================================================
// ADDITIONAL FUNCTIONS TO REACH ~1000 LINES
// ============================================================================

/// Check if all accounts in array are active
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::requires::accounts.len() > 0"]
pub fn all_accounts_active(accounts: &[Account]) -> bool {
    accounts.iter().all(|a| a.is_active)
}

/// Count accounts with balance above threshold
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::requires::accounts.len() > 0"]
#[doc = "rust_fv::ensures::result <= accounts.len()"]
pub fn count_above_threshold(accounts: &[Account], threshold: Balance) -> usize {
    accounts.iter().filter(|a| a.balance.0 > threshold.0).count()
}

/// Calculate total balance for specific account type
#[doc = "rust_fv::requires::accounts.len() > 0"]
pub fn total_balance_by_type(accounts: &[Account], account_type: AccountType) -> Balance {
    let mut total = 0i64;
    for account in accounts {
        if account.account_type == account_type {
            total += account.balance.0;
        }
    }
    Balance(total)
}

/// Freeze account (deactivate)
pub fn freeze_account(account: &mut Account) {
    account.is_active = false;
}

/// Unfreeze account (reactivate)
pub fn unfreeze_account(account: &mut Account) {
    account.is_active = true;
}

/// Check if balance is within tolerance of target
#[doc = "rust_fv::pure"]
pub fn is_within_tolerance(balance: Balance, target: Balance, tolerance: Balance) -> bool {
    let diff = abs_diff(balance.0, target.0);
    diff <= tolerance.0
}

/// Calculate fee for transaction
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::requires::fee_rate <= 100"]
pub fn calculate_fee(amount: Balance, fee_rate: u32) -> Balance {
    let fee = (amount.0 * fee_rate as i64) / 100;
    Balance(fee)
}

/// Check if account qualifies for premium features
#[doc = "rust_fv::pure"]
pub fn is_premium_account(account: &Account, min_balance: Balance) -> bool {
    account.is_active && account.balance.0 >= min_balance.0
}

/// Update account type
pub fn update_account_type(account: &mut Account, new_type: AccountType) {
    account.account_type = new_type;
}

/// Verify transaction timestamp is valid
#[doc = "rust_fv::pure"]
#[doc = "rust_fv::requires::current_time > 0"]
pub fn is_valid_timestamp(transaction: &Transaction, current_time: u64) -> bool {
    transaction.timestamp <= current_time
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_account_creation() {
        let id = AccountId::new(1);
        let balance = Balance::new(1000);
        let account = Account::new(id, AccountType::Checking, balance);
        assert_eq!(account.balance.0, 1000);
        assert!(account.is_active);
    }

    #[test]
    fn test_deposit() {
        let id = AccountId::new(1);
        let balance = Balance::new(1000);
        let mut account = Account::new(id, AccountType::Checking, balance);
        deposit(&mut account, Balance::new(500));
        assert_eq!(account.balance.0, 1500);
    }

    #[test]
    fn test_withdraw() {
        let id = AccountId::new(1);
        let balance = Balance::new(1000);
        let mut account = Account::new(id, AccountType::Checking, balance);
        withdraw(&mut account, Balance::new(300));
        assert_eq!(account.balance.0, 700);
    }

    #[test]
    fn test_transfer() {
        let mut from = Account::new(AccountId::new(1), AccountType::Checking, Balance::new(1000));
        let mut to = Account::new(AccountId::new(2), AccountType::Savings, Balance::new(500));
        transfer(&mut from, &mut to, Balance::new(200));
        assert_eq!(from.balance.0, 800);
        assert_eq!(to.balance.0, 700);
    }

    #[test]
    fn test_utility_functions() {
        assert_eq!(clamp(5, 0, 10), 5);
        assert_eq!(clamp(-5, 0, 10), 0);
        assert_eq!(abs_diff(10, 5), 5);
        assert_eq!(safe_divide(10, 2), 5);
        assert_eq!(safe_divide(10, 0), 0);
    }
}
