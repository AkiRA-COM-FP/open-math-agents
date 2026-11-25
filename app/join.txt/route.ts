import { joinText } from "@/lib/join";
export const revalidate = 3600;
export function GET() {
  return new Response(joinText(), { headers: { "Content-Type": "text/plain; charset=utf-8", "Cache-Control": "public, s-maxage=600" } });
}
