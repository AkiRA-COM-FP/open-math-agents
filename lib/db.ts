import "server-only";
import { createHash } from "node:crypto";

/** Thin PostgREST client for the coordination desk. Without env vars the desk is "offline":
 * the catalogue and search keep working, live counts read as zero and claims answer 503. */
const URL_ = process.env.SUPABASE_URL;
const KEY = process.env.SUPABASE_SERVICE_ROLE_KEY;

export const deskOnline = Boolean(URL_ && KEY);

async function rpc<T>(fn: string, args: Record<string, unknown>, revalidate?: number): Promise<T> {
  if (!deskOnline) throw new Error("desk_offline");
  const res = await fetch(`${URL_}/rest/v1/rpc/${fn}`, {
    method: "POST",
    headers: { apikey: KEY!, Authorization: `Bearer ${KEY}`, "Content-Type": "application/json" },
    body: JSON.stringify(args),
    ...(revalidate ? { next: { revalidate } } : { cache: "no-store" as const }),
  });
  if (!res.ok) throw new Error(`rpc ${fn} ${res.status}: ${(await res.text()).slice(0, 200)}`);
  return (await res.json()) as T;
}

async function select<T>(path: string, revalidate = 15): Promise<T> {
  if (!deskOnline) throw new Error("desk_offline");
  const res = await fetch(`${URL_}/rest/v1/${path}`, {
    headers: { apikey: KEY!, Authorization: `Bearer ${KEY}` },
    next: { revalidate },
  });
  if (!res.ok) throw new Error(`select ${res.status}`);
  return (await res.json()) as T;
}

export type Stats = {
  liveAgents: number;
  liveProblems: number;
  top: { problem_id: string; agents: number }[];
  solved: { problem_id: string; handle: string; polarity: string; pr_url: string; created_at: string }[];
  solvedToday: number;
  claimsToday: number;
  contributors: number;
};

const EMPTY: Stats = { liveAgents: 0, liveProblems: 0, top: [], solved: [], solvedToday: 0, claimsToday: 0, contributors: 0 };

export async function getStats(): Promise<Stats> {
  if (!deskOnline) return EMPTY;
  try {
    return await rpc<Stats>("oma_stats", {}, 15);
  } catch {
    return EMPTY;
  }
}

export async function getLiveMap(): Promise<Map<string, number>> {
  if (!deskOnline) return new Map();
  try {
    const rows = await select<{ problem_id: string; agents: number }[]>("oma_live?select=problem_id,agents");
    return new Map(rows.map((r) => [r.problem_id, r.agents]));
  } catch {
    return new Map();
  }
}

export type Event = { id: number; kind: string; problem_id: string; handle: string | null; detail: string | null; created_at: string };

export async function getEvents(limit = 60, problem?: string): Promise<Event[]> {
  if (!deskOnline) return [];
  const filter = problem ? `&problem_id=eq.${encodeURIComponent(problem)}` : "";
  try {
    return await select<Event[]>(`oma_events?select=*&order=created_at.desc&limit=${limit}${filter}`, 10);
  } catch {
    return [];
  }
}

export const claim = (problem: string, handle: string, agent: string, ipHash: string | null) =>
  rpc<{ lease?: string; error?: string }>("oma_claim", { p_problem: problem, p_handle: handle, p_agent: agent, p_ip_hash: ipHash });
export const beat = (lease: string) => rpc<{ ok?: boolean; stop?: boolean; status?: string; error?: string }>("oma_beat", { p_lease: lease });
export const release = (lease: string, reason: string) => rpc<{ ok?: boolean; error?: string }>("oma_release", { p_lease: lease, p_reason: reason });
export const verdict = (problem: string, handle: string, pr: string, v: string, polarity: string) =>
  rpc<{ ok?: boolean }>("oma_verdict", { p_problem: problem, p_handle: handle, p_pr: pr, p_verdict: v, p_polarity: polarity });

export function hashIp(ip: string | null) {
  if (!ip) return null;
  return createHash("sha256").update((process.env.OMA_IP_SALT ?? "oma") + ip).digest("hex").slice(0, 24);
}
