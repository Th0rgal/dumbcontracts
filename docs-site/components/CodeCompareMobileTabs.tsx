'use client'

import { useEffect, useState } from 'react'

export function CodeCompareMobileTabs() {
  const [active, setActive] = useState<'verity' | 'solidity'>('verity')

  useEffect(() => {
    const root = document.querySelector('.code-compare')
    if (!root) return
    root.querySelectorAll<HTMLElement>('[data-panel]').forEach((panel) => {
      panel.dataset.mobileActive = panel.dataset.panel === active ? 'true' : 'false'
    })
  }, [active])

  return (
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
  )
}
