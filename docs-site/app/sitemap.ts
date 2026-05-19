import type { MetadataRoute } from 'next'

const ROUTES = [
  '',
  '/getting-started',
  '/examples',
  '/core',
  '/add-contract',
  '/compiler',
  '/verification',
  '/edsl-api-reference',
  '/research',
  '/research/iterations',
  '/guides/first-contract',
  '/guides/solidity-to-verity',
  '/guides/production-solidity-patterns',
  '/guides/debugging-proofs',
  '/guides/linking-libraries',
  '/guides/verity-syntax-highlighting',
]

export default function sitemap(): MetadataRoute.Sitemap {
  const base = 'https://veritylang.com'
  const lastModified = new Date()
  return ROUTES.map((path) => ({
    url: `${base}${path}`,
    lastModified,
    changeFrequency: path === '' ? 'weekly' : 'monthly',
    priority: path === '' ? 1.0 : 0.7,
  }))
}
