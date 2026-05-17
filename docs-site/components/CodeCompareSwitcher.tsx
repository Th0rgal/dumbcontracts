'use client'

import { useEffect, useRef, useState } from 'react'

type Lang = 'solidity' | 'verity'

const AUTO_SWITCH_DELAY_MS = 3200

const captions: Record<Lang, { kicker: string; label: string }> = {
  solidity: {
    kicker: 'Solidity',
    label: 'Runtime implementation surface',
  },
  verity: {
    kicker: 'Verity',
    label: 'Typed contract, proof-visible behavior',
  },
}

export function CodeCompareSwitcher({
  verityHtml,
  solidityHtml,
}: {
  verityHtml: string
  solidityHtml: string
}) {
  // Start on Solidity so visitors land on the familiar surface,
  // then briefly lift to Verity as a demonstration.
  const [active, setActive] = useState<Lang>('solidity')
  const rootRef = useRef<HTMLDivElement>(null)
  const interactedRef = useRef(false)
  const autoSwitchedRef = useRef(false)

  useEffect(() => {
    if (interactedRef.current || autoSwitchedRef.current) return
    if (typeof window === 'undefined') return
    const prefersReducedMotion = window.matchMedia('(prefers-reduced-motion: reduce)').matches
    if (prefersReducedMotion) return

    // Wait until the switcher is actually visible before firing the
    // auto-switch — otherwise users who scroll down miss the lift.
    let timer: number | undefined
    const observer = new IntersectionObserver(
      (entries) => {
        for (const entry of entries) {
          if (entry.isIntersecting && !interactedRef.current && !autoSwitchedRef.current) {
            timer = window.setTimeout(() => {
              if (interactedRef.current) return
              autoSwitchedRef.current = true
              setActive('verity')
            }, AUTO_SWITCH_DELAY_MS)
            observer.disconnect()
            break
          }
        }
      },
      { threshold: 0.4 },
    )
    if (rootRef.current) observer.observe(rootRef.current)
    return () => {
      observer.disconnect()
      if (timer !== undefined) window.clearTimeout(timer)
    }
  }, [])

  const pick = (lang: Lang) => {
    interactedRef.current = true
    setActive(lang)
  }

  return (
    <div ref={rootRef} className="code-switcher" data-active={active}>
      <div className="code-switcher__head">
        <div className="code-switcher__caption">
          <span className="code-switcher__kicker">{captions[active].kicker}</span>
          <strong>{captions[active].label}</strong>
        </div>
        <div className="code-switcher__tabs" role="tablist" aria-label="Compare languages">
          <button
            type="button"
            role="tab"
            aria-selected={active === 'solidity'}
            data-active={active === 'solidity'}
            onClick={() => pick('solidity')}
          >
            Solidity
          </button>
          <button
            type="button"
            role="tab"
            aria-selected={active === 'verity'}
            data-active={active === 'verity'}
            onClick={() => pick('verity')}
          >
            Verity
          </button>
        </div>
      </div>
      <div className="code-switcher__panels">
        <figure
          className="code-panel code-panel--solidity"
          data-active={active === 'solidity'}
          aria-hidden={active !== 'solidity'}
        >
          <div className="code-panel__pre" dangerouslySetInnerHTML={{ __html: solidityHtml }} />
        </figure>
        <figure
          className="code-panel code-panel--verity"
          data-active={active === 'verity'}
          aria-hidden={active !== 'verity'}
        >
          <div className="code-panel__pre" dangerouslySetInnerHTML={{ __html: verityHtml }} />
        </figure>
      </div>
    </div>
  )
}
