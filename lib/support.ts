/** Where the Support button sends people: a Stripe Payment Link with "customer chooses the amount"
 *  (NEXT_PUBLIC_SUPPORT_URL), else the sponsor link, else nothing (the page explains how to help otherwise). */
export const SUPPORT_URL: string | null = process.env.NEXT_PUBLIC_SUPPORT_URL || process.env.NEXT_PUBLIC_SPONSOR_URL || null;
