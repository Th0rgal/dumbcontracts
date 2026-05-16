export function ReportCallout({
  title,
  children,
}: {
  title: string
  children: React.ReactNode
}) {
  return (
    <aside className="report-callout">
      <strong>{title}</strong>
      <div>{children}</div>
    </aside>
  )
}
