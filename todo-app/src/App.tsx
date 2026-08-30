import { useEffect, useRef, useState } from 'react'
import './App.css'

const emojis = ['😀', '🥳', '✨', '🌈', '🚀', '💖', '🔥', '🍕', '🦄', '🎉', '🌸', '😎']

type Particle = {
  id: string
  emoji: string
  x: number
  y: number
  angle: number
  distance: number
  rotation: number
  size: number
}

function App() {
  const [selectedEmoji, setSelectedEmoji] = useState(emojis[0])
  const [randomMode, setRandomMode] = useState(false)
  const [particles, setParticles] = useState<Particle[]>([])
  const [isLaunching, setIsLaunching] = useState(false)
  const holdTimer = useRef<number | null>(null)
  const particleId = useRef(0)

  const stopLaunching = () => {
    if (holdTimer.current !== null) {
      window.clearInterval(holdTimer.current)
      holdTimer.current = null
    }
    setIsLaunching(false)
  }

  useEffect(() => stopLaunching, [])

  const launchBurst = (x: number, y: number) => {
    const burst = Array.from({ length: 16 }, (_, index) => {
      const angle = (360 / 16) * index + Math.random() * 14 - 7
      return {
        id: `${particleId.current++}`,
        emoji: randomMode ? emojis[Math.floor(Math.random() * emojis.length)] : selectedEmoji,
        x,
        y,
        angle,
        distance: 90 + Math.random() * 180,
        rotation: Math.random() * 720 - 360,
        size: 24 + Math.random() * 18,
      }
    })

    setParticles(current => [...current, ...burst])
    window.setTimeout(() => {
      const ids = new Set(burst.map(particle => particle.id))
      setParticles(current => current.filter(particle => !ids.has(particle.id)))
    }, 900)
  }

  const handlePointerDown = (event: React.PointerEvent<HTMLDivElement>) => {
    event.currentTarget.setPointerCapture(event.pointerId)
    launchBurst(event.clientX, event.clientY)
    setIsLaunching(true)
    holdTimer.current = window.setInterval(() => launchBurst(event.clientX, event.clientY), 220)
  }

  return (
    <main className="launcher">
      <section className="control-panel" aria-label="Emoji launcher controls">
        <p className="eyebrow">Emoji blaster</p>
        <h1>Make it rain</h1>
        <p className="instructions">Tap and hold anywhere to launch a burst.</p>

        <div className="picker" aria-label="Choose an emoji">
          {emojis.map(emoji => (
            <button
              className={`emoji-option ${selectedEmoji === emoji && !randomMode ? 'selected' : ''}`}
              key={emoji}
              type="button"
              onClick={() => {
                setSelectedEmoji(emoji)
                setRandomMode(false)
              }}
              aria-label={`Launch ${emoji}`}
              aria-pressed={selectedEmoji === emoji && !randomMode}
            >
              {emoji}
            </button>
          ))}
        </div>

        <button
          className={`random-toggle ${randomMode ? 'active' : ''}`}
          type="button"
          onClick={() => setRandomMode(enabled => !enabled)}
          aria-pressed={randomMode}
        >
          <span>🎲</span> Random mode
        </button>
      </section>

      <div
        className={`launch-area ${isLaunching ? 'launching' : ''}`}
        onPointerDown={handlePointerDown}
        onPointerUp={stopLaunching}
        onPointerCancel={stopLaunching}
        onLostPointerCapture={stopLaunching}
        role="button"
        tabIndex={0}
        aria-label="Tap and hold to launch emojis"
        onKeyDown={event => {
          if (event.key === 'Enter' || event.key === ' ') {
            event.preventDefault()
            const bounds = event.currentTarget.getBoundingClientRect()
            launchBurst(bounds.left + bounds.width / 2, bounds.top + bounds.height / 2)
          }
        }}
      >
        <div className="target">
          <span>{randomMode ? '🎲' : selectedEmoji}</span>
          <p>{isLaunching ? 'Keep holding!' : 'Press anywhere'}</p>
        </div>
      </div>

      <div className="particle-layer" aria-hidden="true">
        {particles.map(particle => (
          <span
            className="particle"
            key={particle.id}
            style={{
              '--x': `${particle.x}px`,
              '--y': `${particle.y}px`,
              '--angle': `${particle.angle}deg`,
              '--distance': `${particle.distance}px`,
              '--rotation': `${particle.rotation}deg`,
              fontSize: `${particle.size}px`,
            } as React.CSSProperties}
          >
            {particle.emoji}
          </span>
        ))}
      </div>
    </main>
  )
}

export default App
