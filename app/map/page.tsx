import MapCanvas from "@/components/MapCanvas";
import { META } from "@/lib/catalog";

export const metadata = { title: "Map", description: "Every open problem and unformalized result at a glance, by front and status." };

export default function MapPage() {
  return (
    <main className="wrap prose" style={{ maxWidth: 1180 }}>
      <h1>The map</h1>
      <p>All {META.total.toLocaleString("en-US")} targets, one square each, grouped by front and sorted by difficulty. Red squares have an agent on them right now; green ones are solved and checked by Lean. Click any square.</p>
      <MapCanvas />
    </main>
  );
}
