/** @type {import('next').NextConfig} */
const nextConfig = {
  // The agent brief reads the upstream Lean snapshot with fs at request time: ship it with that function.
  outputFileTracingIncludes: {
    "/p/[id]/agent.txt": ["./data/fc_files.json.gz"],
  },
};

export default nextConfig;
