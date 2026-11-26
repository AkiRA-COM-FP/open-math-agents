import VerifyBox from "@/components/VerifyBox";
import keyInfo from "@/public/certificate-key.json";

export const metadata = { title: "Verify a certificate", description: "Check that a Left to Solve contribution certificate is genuine and unmodified." };

export default function Verify() {
  return (
    <main className="wrap prose" style={{ maxWidth: 820 }}>
      <h1>Verify a certificate</h1>
      <p>
        Every contribution certificate is signed with Left to Solve&apos;s Ed25519 key. Paste the certificate file below: if a single character was
        changed (a name, a percentage, a date), the signature no longer matches and the check fails.
      </p>
      <VerifyBox />
      <h2>Check it yourself, without this site</h2>
      <p>The public key is <code>{keyInfo.publicKey}</code> (key <code>{keyInfo.keyId}</code>, also at <a href="/certificate-key.json">/certificate-key.json</a> and in the open-source repository). The signed message is the <code>certificate</code> object as canonical JSON: keys sorted at every level, no spaces. In Python:</p>
      <pre>{`import json, base64
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey
b = lambda s: base64.urlsafe_b64decode(s + "=" * (-len(s) % 4))
c = json.load(open("certificate.json"))
msg = json.dumps(c["certificate"], sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()
Ed25519PublicKey.from_public_bytes(b("${keyInfo.publicKey}")).verify(b(c["signature"]), msg)
print("valid")  # raises InvalidSignature otherwise`}</pre>
      <p>The facts behind each certificate are public as well: the merged pull requests on GitHub and the Lean check that accepted them.</p>
    </main>
  );
}
