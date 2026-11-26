import NextLink from "next/link";
import type { ComponentProps } from "react";

/** next/link without viewport prefetching. A results list shows 30+ links; prefetching each one cost ~20 extra
 *  CDN requests per page view, which is what Vercel bills. Navigation stays client-side, just fetched on click. */
export default function Link(props: ComponentProps<typeof NextLink>) {
  return <NextLink prefetch={false} {...props} />;
}
