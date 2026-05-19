import { Layout, Navbar } from 'nextra-theme-docs'
import { Head } from 'nextra/components'
import { getPageMap } from 'nextra/page-map'
import 'nextra-theme-docs/style.css'
import './verity-site.css'
import './verity-code.css'

const SITE_URL = 'https://veritylang.com'
const SITE_TITLE = 'Verity'
const SITE_DESCRIPTION =
  'A Lean-native EDSL for verified smart contracts. Write the spec, write the implementation, and prove they agree — every claim is machine-checked at compile time.'

export const metadata = {
  metadataBase: new URL(SITE_URL),
  title: {
    default: SITE_TITLE,
    template: '%s',
  },
  description: SITE_DESCRIPTION,
  icons: {
    icon: '/verity.svg',
    shortcut: '/verity.svg',
    apple: '/verity.svg',
  },
  openGraph: {
    type: 'website',
    siteName: SITE_TITLE,
    title: SITE_TITLE,
    description: SITE_DESCRIPTION,
    url: SITE_URL,
    locale: 'en_US',
  },
  twitter: {
    card: 'summary',
    title: SITE_TITLE,
    description: SITE_DESCRIPTION,
  },
}

const navbar = (
  <Navbar
    logo={
      <span className="verity-brand">
        <img src="/verity.svg" alt="" width="22" height="22" />
        <strong>Verity</strong>
      </span>
    }
    projectLink="https://github.com/lfglabs-dev/verity"
  />
)

export default async function RootLayout({ children }: { children: React.ReactNode }) {
  return (
    <html lang="en" dir="ltr" suppressHydrationWarning>
      <Head />
      <body>
        <Layout
          navbar={navbar}
          pageMap={await getPageMap()}
          docsRepositoryBase="https://github.com/lfglabs-dev/verity/tree/main/docs-site"
          sidebar={{ defaultMenuCollapseLevel: 1 }}
          toc={{ backToTop: true }}
        >
          {children}
        </Layout>
      </body>
    </html>
  )
}
