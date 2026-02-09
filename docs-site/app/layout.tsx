import type { Metadata, Viewport } from "next";
import type { ReactNode } from "react";
import { Head } from "nextra/components";
import { ThemeProvider } from "@/components/theme-provider";
import "./globals.css";

export const viewport: Viewport = {
  themeColor: [
    { media: "(prefers-color-scheme: light)", color: "#ffffff" },
    { media: "(prefers-color-scheme: dark)", color: "#0c0b0a" },
  ],
  colorScheme: "light dark",
  width: "device-width",
  initialScale: 1,
  viewportFit: "cover",
};

export const metadata: Metadata = {
  metadataBase: new URL("https://dumbcontracts.vercel.app"),
  title: {
    default: "Dumb Contracts | Auditable Smart Contract Specs",
    template: "%s | Dumb Contracts",
  },
  description:
    "Lean specs + proofs for auditable smart contract rules, compiled toward Yul/EVM.",
  applicationName: "Dumb Contracts",
  generator: "Next.js",
  keywords: [
    "smart contracts",
    "formal verification",
    "lean",
    "yul",
    "evm",
    "specification",
    "proofs",
  ],
  authors: [{ name: "Thomas M." }, { name: "Nico C." }],
  creator: "Dumb Contracts",
  publisher: "Dumb Contracts",
  robots: {
    index: true,
    follow: true,
  },
  twitter: {
    card: "summary_large_image",
    title: "Dumb Contracts",
    description:
      "Lean specs + proofs for auditable smart contract rules, compiled toward Yul/EVM.",
    creator: "@music_music_yo",
    images: ["/og-image.png"],
  },
  openGraph: {
    type: "website",
    locale: "en_US",
    url: "https://dumbcontracts.vercel.app",
    siteName: "Dumb Contracts",
    title: "Dumb Contracts",
    description:
      "Lean specs + proofs for auditable smart contract rules, compiled toward Yul/EVM.",
    images: [
      {
        url: "/og-image.png",
        width: 1200,
        height: 630,
        alt: "Dumb Contracts - Auditable Smart Contract Specs",
      },
    ],
  },
  icons: {
    icon: "/favicon.svg",
    apple: "/apple-touch-icon.png",
  },
  appleWebApp: {
    capable: true,
    statusBarStyle: "black-translucent",
    title: "Dumb Contracts",
  },
  other: {
    "msapplication-TileColor": "#0c0b0a",
  },
};

export default function RootLayout({
  children,
}: {
  children: ReactNode;
}) {
  return (
    <html lang="en" dir="ltr" suppressHydrationWarning>
      <Head>
        <meta
          name="theme-color"
          media="(prefers-color-scheme: light)"
          content="#ffffff"
        />
        <meta
          name="theme-color"
          media="(prefers-color-scheme: dark)"
          content="#0c0b0a"
        />
      </Head>
      <body className="min-h-dvh bg-mesh-subtle">
        <ThemeProvider>{children}</ThemeProvider>
      </body>
    </html>
  );
}
