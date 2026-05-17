export function ReadingList({
  items,
}: {
  items: { href: string; title: string; note: string }[]
}) {
  return (
    <ul className="verity-reading-list" role="list">
      {items.map((item) => (
        <li key={item.href}>
          <a href={item.href} className="verity-reading-list__row">
            <span className="verity-reading-list__title">{item.title}</span>
            <span className="verity-reading-list__note">{item.note}</span>
            <span aria-hidden="true" className="verity-reading-list__arrow">→</span>
          </a>
        </li>
      ))}
    </ul>
  )
}
