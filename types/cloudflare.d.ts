/// <reference types="vite/client" />
// The few Workers runtime types this app uses (the full generated set, in .cloudflare/types, clashes with the DOM lib).
declare module "cloudflare:workers" {
  export const env: Record<string, unknown>;
}
interface D1Result<T> { results: T[] }
interface D1PreparedStatement {
  bind(...values: unknown[]): D1PreparedStatement;
  all<T = Record<string, unknown>>(): Promise<D1Result<T>>;
  first<T = Record<string, unknown>>(): Promise<T | null>;
}
interface D1Database { prepare(query: string): D1PreparedStatement }
