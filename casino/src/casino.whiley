import std::math

// public final int MAX256 = math::pow(2, 256)
public final int MAX256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936
public type uint256 is (int x) where x >= 0 && x < MAX256 
 
/* TODO: add this.  It was not used in base implementation.
public function keccak256(uint256 in) -> (uint256 out):
    return 0 
*/

// 2**160 - solidity addresses are 160-bit integers
public type uint160 is (int x) where x >= 0 && x < 1461501637330902918203684832716283019655932542976

public type Address is {
    uint160 address, // should be immutable, unique
    uint256 balance
}

public type Block is {
    Address coinbase,
    uint256 difficulty,
    uint256 gaslimit, 
    uint256 number,
    uint256 timestamp
}

public type Message is {
    Address sender,
    uint256 gas,
    uint160 data,
    uint256 value
}

public type Transaction is {
    uint256 gasprice,
    Address origin
}

public type Coin is (int x) where x == 0 || x == 1
public final Coin HEADS = 0
public final Coin TAILS = 1

public type State is (int x) where x == 0 || x == 1 || x == 2
public final State IDLE = 0
public final State GAME_AVAILABLE = 1
public final State BET_PLACED = 2 

public type Wager is {
    uint256 value,
    Coin guess,
    uint256 timestamp
}

// main contract state class with all global variables
public type Casino is {
    Address address,
    State state,
    Address operator,
    uint256 pot,
    uint256 timeout,
    uint256 secretNumber,
    Address player,
    Wager wager,
    Message msg,
    Block block,
    Transaction tx,
    bool destroyed
}

// TODO: make this an invariant of the Casino type.
public property valid(Casino casino)
where casino.state == BET_PLACED ==> casino.pot + casino.wager.value == casino.address.balance
where casino.state != BET_PLACED ==> casino.pot == casino.address.balance
where casino.operator.address != casino.address.address
where casino.player.address != casino.address.address
where casino.msg.sender.address != casino.address.address
where casino.block.coinbase.address != casino.address.address
where casino.tx.origin.address != casino.address.address

// executed by address receiving the money which withdraws 'price' from the 'sender' address
public function transfer(Address receiver, Address sender, uint256 price) -> (Address receiver_update, Address sender_update)
requires price <= sender.balance // different in Java, incorrectly
requires sender.address == receiver.address ==> sender.balance == receiver.balance
requires receiver.balance + price < MAX256
ensures receiver_update.address == receiver.address
ensures sender_update.address == sender.address 
ensures sender.address != receiver.address ==> (receiver_update.balance == receiver.balance + price && sender_update.balance == sender.balance - price)
ensures sender.address == receiver.address ==> (sender_update.balance == receiver_update.balance && sender_update.balance == sender.balance):
    if sender.address != receiver.address:
        sender.balance = sender.balance - price
        receiver.balance = receiver.balance + price

    return (receiver, sender)

public function payable(Address receiver, Message msg) -> (Address receiver_update, Address sender_update)
requires msg.value <= msg.sender.balance // different in Java, incorrectly
requires receiver.address == msg.sender.address ==> msg.sender.balance == receiver.balance
requires receiver.balance + msg.value < MAX256
ensures receiver_update.address == receiver.address
ensures sender_update.address == msg.sender.address
ensures receiver.address != msg.sender.address ==> (receiver_update.balance == receiver.balance + msg.value && sender_update.balance == msg.sender.balance - msg.value)
ensures receiver.address == msg.sender.address ==> (receiver_update.balance == sender_update.balance && receiver.balance == receiver_update.balance):
    (receiver, msg.sender) = transfer(receiver, msg.sender, msg.value)
    return (receiver, msg.sender)


function init(uint160 contract_address, Message msg, Block block, Transaction tx) -> (Casino out)
requires contract_address != 0
requires msg.sender.address != contract_address
requires block.coinbase.address != contract_address
requires tx.origin.address != contract_address
ensures valid(out):
    return {
        address: {address: contract_address, balance: 0},
        state: IDLE,
        operator: msg.sender,
        pot: 0,
        timeout: 30,
        secretNumber: 0, // default 
        player: {address: 0, balance: 0}, // default 
        wager: {value: 0, guess: HEADS, timestamp: 0}, // default 
        msg: msg,
        block: block, 
        tx: tx, 
        destroyed: false
    }

public property costs(Casino casino, uint256 value)
where casino.msg.value == value

public property byOperator(Casino casino)
where casino.msg.sender == casino.operator

public property noActiveBet(Casino casino)
where casino.state == IDLE || casino.state == GAME_AVAILABLE

public property inState(Casino casino, State state)
where casino.state == state

public property validCall(Casino casino, Message msg, Block block, Transaction tx)
where msg.sender.address != casino.address.address
where block.coinbase.address != casino.address.address
where tx.origin.address != casino.address.address

function updateBlockChainVariables(Casino casino, Message msg, Block block, Transaction tx) -> (Casino out)
requires valid(casino)
requires validCall(casino, msg, block, tx)
ensures casino.address == out.address
ensures casino.state == out.state
ensures casino.operator == out.operator
ensures casino.pot == out.pot
ensures casino.timeout == out.timeout
ensures casino.secretNumber == out.secretNumber
ensures casino.player == out.player
ensures casino.wager == out.wager
ensures casino.destroyed == out.destroyed
ensures out.msg == msg
ensures out.block == block
ensures out.tx == tx
ensures valid(out):
    casino.msg = msg
    casino.block = block
    casino.tx = tx
    return casino

public function call_updateTimeout(Casino casino, uint256 timeout, Message msg, Block block, Transaction tx) -> (Casino out)
requires valid(casino)
requires validCall(casino, msg, block, tx)
requires msg.sender == casino.operator
requires noActiveBet(casino)
ensures valid(out):
    casino = updateBlockChainVariables(casino, msg, block, tx)
    casino = updateTimeout(casino, timeout)
    return casino

function updateTimeout(Casino casino, uint256 timeout) -> (Casino out)
requires valid(casino)
requires byOperator(casino)
requires noActiveBet(casino)
ensures valid(out)
ensures out.timeout == timeout:
    casino.timeout = timeout
    return casino

public function call_addToPot(Casino casino, uint256 value, Message msg, Block block, Transaction tx) -> (Casino out)
requires valid(casino)
requires validCall(casino, msg, block, tx)
requires msg.sender == casino.operator
requires msg.value == value && value > 0
requires value <= casino.operator.balance
requires casino.address.balance + value < MAX256
ensures out.pot == casino.pot + value
ensures valid(out):
    casino = updateBlockChainVariables(casino, msg, block, tx)
    casino = addToPot(casino, value)
    return casino

function addToPot(Casino casino, uint256 value) -> (Casino out)
requires valid(casino)
requires byOperator(casino)
requires costs(casino, value)
requires value > 0
requires value <= casino.operator.balance
requires casino.address.balance + value < MAX256
ensures out.pot == casino.pot + value
ensures valid(out):
    (casino.address, casino.msg.sender) = payable(casino.address, casino.msg)
    casino.pot = casino.pot + value

    return casino

public function call_removeFromPot(Casino casino, uint256 value, Message msg, Block block, Transaction tx) -> (Casino out)
requires valid(casino)
requires validCall(casino, msg, block, tx)
requires msg.sender == casino.operator
requires noActiveBet(casino) 
requires value > 0 && value <= casino.pot
requires msg.sender.balance + value < MAX256
ensures out.pot == casino.pot - value
ensures out.msg.sender.balance == msg.sender.balance + value
ensures out.address.balance == casino.address.balance - value
ensures valid(out):
    casino = updateBlockChainVariables(casino, msg, block, tx)
    casino = removeFromPot(casino, value)
    return casino

function removeFromPot(Casino casino, uint256 value) -> (Casino out)
requires valid(casino)
requires byOperator(casino)
requires noActiveBet(casino)
requires value > 0 && value <= casino.pot
requires casino.msg.sender.balance + value < MAX256
ensures out.pot == casino.pot - value
ensures out.msg.sender.balance == casino.msg.sender.balance + value
ensures out.address.balance == casino.address.balance - value
ensures valid(out):
    // the following line isn't in the paper's discussion of this transaction & really doesn't make sense & prevents sensible verification
    // (casino.address, casino.msg.sender) = payable(casino.address, casino.msg) 
    casino.pot = casino.pot - value
    (casino.msg.sender, casino.address) = transfer(casino.msg.sender, casino.address, value)
    return casino

public function call_createGame(Casino casino, uint256 secretNumber, Message msg, Block block, Transaction tx) -> (Casino out)
requires validCall(casino, msg, block, tx)
requires valid(casino)
requires inState(casino, IDLE)
requires msg.sender == casino.operator
ensures valid(out):
    casino = updateBlockChainVariables(casino, msg, block, tx)
    casino = createGame(casino, secretNumber)
    return casino

function createGame(Casino casino, uint256 secretNumber) -> (Casino out)
requires valid(casino)
requires byOperator(casino)
requires inState(casino, IDLE)
ensures out.secretNumber == secretNumber
ensures out.state == GAME_AVAILABLE
ensures valid(out): 
    casino.secretNumber = secretNumber
    casino.state = GAME_AVAILABLE
    return casino

public function call_placeBet(Casino casino, uint256 value, Coin guess, Message msg, Block block, Transaction tx) -> (Casino out)
requires validCall(casino, msg, block, tx)
requires valid(casino)
requires inState(casino, GAME_AVAILABLE)
requires msg.sender.address != casino.operator.address
requires value > 0 && value <= casino.pot
requires msg.value == value
requires value <= msg.sender.balance
requires casino.address.balance + value < MAX256
ensures valid(out)
ensures out.state == BET_PLACED
ensures out.player.address == msg.sender.address
ensures out.wager.value == value
ensures out.wager.guess == guess
ensures out.wager.timestamp == block.timestamp:
    casino = updateBlockChainVariables(casino, msg, block, tx)
    casino = placeBet(casino, value, guess)
    return casino

function placeBet(Casino casino, uint256 value, Coin guess) -> (Casino out)
requires valid(casino)
requires costs(casino, value)
requires inState(casino, GAME_AVAILABLE)
requires casino.msg.sender.address != casino.operator.address
requires value > 0 && value <= casino.pot
requires value <= casino.msg.sender.balance
requires casino.address.balance + value < MAX256
ensures out.state == BET_PLACED
ensures out.player.address == casino.msg.sender.address
ensures out.wager.value == value
ensures out.wager.guess == guess
ensures out.wager.timestamp == casino.block.timestamp
ensures valid(out):
    (casino.address, casino.msg.sender) = payable(casino.address, casino.msg)
    casino.state = BET_PLACED
    casino.player = casino.msg.sender
    casino.wager = {
        value: value,
        guess: guess,
        timestamp: casino.block.timestamp
    }
    return casino

public function call_decideBet(Casino casino, uint256 publicNumber, Message msg, Block block, Transaction tx) -> (Casino out)
requires validCall(casino, msg, block, tx)
requires valid(casino)
requires inState(casino, BET_PLACED)
requires msg.sender == casino.operator
requires (publicNumber % 2 == 0 <==> casino.wager.guess == HEADS) ==>
(casino.wager.value * 2 <= casino.address.balance && casino.wager.value * 2 + casino.player.balance < MAX256)
//requires casino.secretNumber == keccak256(publicNumber) // ignore for now since hashfunction not implemented
ensures (publicNumber % 2 == 0 <==> casino.wager.guess == HEADS) ==>
(out.pot == casino.pot - casino.wager.value && out.address.balance == casino.address.balance - casino.wager.value * 2)
ensures !(publicNumber % 2 == 0 <==> casino.wager.guess == HEADS) ==> out.pot == casino.pot + casino.wager.value
ensures out.wager.value == 0
ensures out.state == IDLE
ensures valid(out):
    casino = updateBlockChainVariables(casino, msg, block, tx)
    casino = decideBet(casino, publicNumber)
    return casino

function decideBet(Casino casino, uint256 publicNumber) -> (Casino out)
requires valid(casino)
requires byOperator(casino)
requires inState(casino, BET_PLACED)
requires (publicNumber % 2 == 0 <==> casino.wager.guess == HEADS) ==>
(casino.wager.value * 2 <= casino.address.balance && casino.wager.value * 2 + casino.player.balance < MAX256)
//requires casino.secretNumber == keccak256(publicNumber) // ignore for now since hashfunction not implemented
ensures (publicNumber % 2 == 0 <==> casino.wager.guess == HEADS) ==>
(out.pot == casino.pot - casino.wager.value && out.address.balance == casino.address.balance - casino.wager.value * 2)
ensures !(publicNumber % 2 == 0 <==> casino.wager.guess == HEADS) ==> out.pot == casino.pot + casino.wager.value
ensures out.wager.value == 0
ensures out.state == IDLE
ensures valid(out):
    Coin secret
    if (publicNumber % 2 == 0):
        secret = HEADS
    else:
        secret = TAILS
    
    if (secret == casino.wager.guess):
        casino = playerWins(casino)
    else:
        casino = operatorWins(casino)
    casino.state = IDLE
    return casino

public function call_timeoutBet(Casino casino, Message msg, Block block, Transaction tx) -> (Casino out)
requires validCall(casino, msg, block, tx)
requires inState(casino, BET_PLACED)
requires block.timestamp - casino.wager.timestamp > casino.timeout
requires msg.sender == casino.player
requires valid(casino)
requires casino.wager.value * 2 <= casino.address.balance
requires casino.wager.value * 2 + casino.player.balance < MAX256
ensures out.pot == casino.pot - casino.wager.value
ensures out.state == IDLE
ensures valid(out):
    casino = updateBlockChainVariables(casino, msg, block, tx)
    casino = timeoutBet(casino)
    return casino

function timeoutBet(Casino casino) -> (Casino out)
requires valid(casino)
requires inState(casino, BET_PLACED)
requires casino.msg.sender == casino.player
requires casino.block.timestamp - casino.wager.timestamp > casino.timeout
requires casino.wager.value * 2 <= casino.address.balance
requires casino.wager.value * 2 + casino.player.balance < MAX256
ensures out.pot == casino.pot - casino.wager.value
ensures out.state == IDLE
ensures valid(out):
    casino = playerWins(casino)
    casino.state = IDLE
    return casino

function playerWins(Casino casino) -> (Casino out)
requires valid(casino)
requires inState(casino, BET_PLACED)
requires casino.wager.value * 2 <= casino.address.balance
requires casino.wager.value * 2 + casino.player.balance < MAX256
ensures out.pot == casino.pot - casino.wager.value
ensures out.player.balance == casino.player.balance + casino.wager.value * 2
ensures out.wager.value == 0
ensures out.address.balance == casino.address.balance - casino.wager.value * 2
ensures valid(out):
    casino.pot = casino.pot - casino.wager.value
    (casino.player, casino.address) = transfer(casino.player, casino.address, casino.wager.value * 2)
    casino.wager.value = 0
    return casino

function operatorWins(Casino casino) -> (Casino out)
requires inState(casino, BET_PLACED)
requires valid(casino)
ensures out.pot == casino.pot + casino.wager.value
ensures out.wager.value == 0
ensures valid(out):
    casino.pot = casino.pot + casino.wager.value
    casino.wager.value = 0
    return casino

public function call_closeCasino(Casino casino, Message msg, Block block, Transaction tx) -> (Casino out)
requires valid(casino)
requires validCall(casino, msg, block, tx)
requires inState(casino, IDLE)
requires msg.sender == casino.operator
requires casino.operator.balance + casino.address.balance < MAX256
ensures out.operator.balance == casino.operator.balance + casino.address.balance
ensures out.address.balance == 0
ensures out.destroyed:
    casino = updateBlockChainVariables(casino, msg, block, tx)
    casino = closeCasino(casino)
    return casino

function closeCasino(Casino casino) -> (Casino out)
requires valid(casino)
requires inState(casino, IDLE)
requires byOperator(casino)
requires casino.operator.balance + casino.address.balance < MAX256
ensures out.operator.balance == casino.operator.balance + casino.address.balance
ensures out.address.balance == 0
ensures out.destroyed:
    Address operator_update
    (casino, operator_update) = selfdestruct(casino, casino.operator)
    casino.operator = operator_update
    return casino
    
function selfdestruct(Casino casino, Address a) -> (Casino out, Address receiver)
requires valid(casino)
requires casino.address.address != a.address
requires a.balance + casino.address.balance < MAX256
ensures receiver.balance == a.balance + casino.address.balance 
ensures out.address.balance == 0
ensures out.destroyed:
    (a, casino.address) = transfer(a, casino.address, casino.address.balance)
    casino.destroyed = true
    return (casino, a)
