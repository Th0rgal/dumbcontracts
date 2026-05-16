'use client'

import { useState } from 'react'

const verityCode = `verity_contract Escrow where
  storage
    owner : Address := slot 0
    balances : Address -> Uint256 := slot 1

  event_defs
    Deposited(Address, Uint256)
    Withdrawn(Address, Uint256)

  linked_externals
    external auditHook(Address, Uint256) -> (Bool)

  modifier onlyOwner := do
    let sender <- msgSender
    let currentOwner <- getStorageAddr owner
    requireError (sender == currentOwner) Unauthorized()

  function deposit () : Unit := do
    let sender <- msgSender
    let amount <- msgValue
    let current <- getMapping balances sender
    let next <- requireSomeUint (safeAdd current amount) BalanceOverflow()
    setMapping balances sender next
    emit "Deposited" [sender.toNat, amount.toNat]

  function withdraw (amount : Uint256) with onlyOwner : Unit := do
    let sender <- msgSender
    let current <- getMapping balances sender
    requireError (amount <= current) InsufficientBalance()
    let ok <- externalCall auditHook [sender, amount]
    requireError ok AuditRejected()
    setMapping balances sender (current - amount)
    emit "Withdrawn" [sender.toNat, amount.toNat]`

const solidityCode = `contract Escrow {
    address public owner;
    mapping(address => uint256) public balances;

    event Deposited(address indexed account, uint256 amount);
    event Withdrawn(address indexed account, uint256 amount);

    modifier onlyOwner() {
        require(msg.sender == owner, "UNAUTHORIZED");
        _;
    }

    function deposit() external payable {
        balances[msg.sender] += msg.value;
        emit Deposited(msg.sender, msg.value);
    }

    function withdraw(uint256 amount) external onlyOwner {
        require(amount <= balances[msg.sender], "INSUFFICIENT_BALANCE");
        bool ok = auditHook(msg.sender, amount);
        require(ok, "AUDIT_REJECTED");
        balances[msg.sender] -= amount;
        emit Withdrawn(msg.sender, amount);
    }
}`

const notes = [
  'Reusable modifiers are ordinary verified helpers, not compiler magic.',
  'Typed external calls expose oracle and ABI assumptions at the language boundary.',
  'Event definitions and storage slots remain visible to specs, proofs, and compiler reports.',
]

export function CodeCompare() {
  const [active, setActive] = useState<'verity' | 'solidity'>('verity')

  return (
    <section className="code-compare" aria-labelledby="code-compare-title">
      <div className="code-compare__intro">
        <p className="verity-kicker">Semantic contract surface</p>
        <h2 id="code-compare-title">Solidity patterns, lifted into proof-carrying code.</h2>
        <p>
          Verity keeps production smart-contract structure recognizable while making guards,
          ABI projection, event emission, and external calls available to Lean proofs.
        </p>
      </div>
      <div className="code-compare__switch" role="tablist" aria-label="Compare languages">
        <button
          type="button"
          role="tab"
          aria-selected={active === 'verity'}
          onClick={() => setActive('verity')}
        >
          Verity
        </button>
        <button
          type="button"
          role="tab"
          aria-selected={active === 'solidity'}
          onClick={() => setActive('solidity')}
        >
          Solidity
        </button>
      </div>
      <div className="code-compare__grid">
        <figure className="code-panel code-panel--verity" data-mobile-active={active === 'verity'}>
          <figcaption>
            <span>Verity</span>
            <strong>Typed contract, proof-visible behavior</strong>
          </figcaption>
          <pre data-language="verity"><code>{verityCode}</code></pre>
        </figure>
        <figure className="code-panel code-panel--solidity" data-mobile-active={active === 'solidity'}>
          <figcaption>
            <span>Solidity</span>
            <strong>Runtime implementation surface</strong>
          </figcaption>
          <pre data-language="solidity"><code>{solidityCode}</code></pre>
        </figure>
      </div>
      <ul className="code-compare__notes">
        {notes.map((note) => (
          <li key={note}>{note}</li>
        ))}
      </ul>
    </section>
  )
}
