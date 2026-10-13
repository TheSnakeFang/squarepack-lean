#!/usr/bin/env python3
"""Convert a rational certificate (`n S` or `n W H` header, lines `x y t`) into Lean data and
kernel-check chunk files for `Sqlean/CheckCore.lean`.

  gen_cert.py CERT NAME --W 19 [--H 18] [--sq 10000] [--pairs 20000] [--per-file 4]

The box is `[0, W - 1/sq] x [0, H - 1/sq]` (H defaults to W): the target side, not the
certificate's own header, which must be smaller (checked here).  Writes
`Sqlean/Data/NAME.lean` (data), `Sqlean/Data/NAME/Chk*.lean` (kernel checks) and prints
statistics.  An exact mirror of the Lean checker runs first; generation stops if it fails.
"""
import argparse
import hashlib
import os
import sys
from fractions import Fraction as F
from math import gcd, lcm

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def read_cert(path):
    hdr, rows = None, []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            parts = line.split()
            if hdr is None:
                hdr = [F(p) for p in parts]
            else:
                rows.append(tuple(F(p) for p in parts))
    assert int(hdr[0]) == len(rows)
    return hdr, rows


def to_int(rows):
    D = 1
    Q = 1
    for x, y, t in rows:
        D = lcm(D, x.denominator, y.denominator)
        Q = lcm(Q, t.denominator)
    sqs = []
    for x, y, t in rows:
        X = x * D
        Y = y * D
        P = t * Q
        assert X.denominator == 1 and Y.denominator == 1 and P.denominator == 1
        X, Y, P = int(X), int(Y), int(P)
        C, S, N = Q * Q - P * P, 2 * P * Q, Q * Q + P * P
        g = gcd(gcd(C, S), N)
        sqs.append((X, Y, C // g, S // g, N // g))
    return D, sqs


# ---- exact mirror of CheckCore.lean ----
def unit_ok(q):
    X, Y, C, S, N = q
    return C * C + S * S == N * N and N > 0


def corner_ok(D, Wn, Hn, Sd, q, ea, eb):
    X, Y, C, S, N = q
    vx = 2 * N * X + D * (ea * C - eb * S)
    vy = 2 * N * Y + D * (ea * S + eb * C)
    M = 2 * N * D
    return 0 <= vx and vx * Sd <= M * Wn and 0 <= vy and vy * Sd <= M * Hn


def box_ok(D, Wn, Hn, Sd, q):
    return all(corner_ok(D, Wn, Hn, Sd, q, ea, eb) for ea, eb in ((1, 1), (1, -1), (-1, 1), (-1, -1)))


def nAB(C, S, k):
    return [(C, S), (-S, C), (-C, -S), (S, -C)][k]


def far_ok(D, i, j):
    dx, dy = j[0] - i[0], j[1] - i[1]
    return 2 * D * D < dx * dx + dy * dy


def sep_ok(D, i, j, k):
    A, B = nAB(i[2], i[3], k)
    u = A * j[2] + B * j[3]
    v = B * j[2] - A * j[3]
    return i[4] * j[4] * D + D * (abs(u) + abs(v)) <= 2 * j[4] * (A * (j[0] - i[0]) + B * (j[1] - i[1]))


def pair_ok(D, i, j):
    if far_ok(D, i, j):
        return 'far'
    for k in range(4):
        if sep_ok(D, i, j, k):
            return 'sep'
    for k in range(4):
        if sep_ok(D, j, i, k):
            return 'sep'
    return None


def lean_int(v):
    return str(v) if v >= 0 else '(%d)' % v


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cert')
    ap.add_argument('name')
    ap.add_argument('--W', type=int, required=True)
    ap.add_argument('--H', type=int)
    ap.add_argument('--sq', type=int, default=10000)
    ap.add_argument('--pairs', type=int, default=3000, help='target row tests per chunk')
    ap.add_argument('--per-file', type=int, default=1, help='chunk theorems per file')
    a = ap.parse_args()
    H = a.H if a.H is not None else a.W
    hdr, rows = read_cert(a.cert)
    n = len(rows)
    Wt, Ht = F(a.W) - F(1, a.sq), F(H) - F(1, a.sq)
    cw = hdr[1]
    ch = hdr[2] if len(hdr) > 2 else hdr[1]
    assert cw <= Wt and ch <= Ht, ('certificate side exceeds target', float(cw), float(ch))
    D, sqs = to_int(rows)
    sqs.sort(key=lambda q: (q[0], q[1]))
    Wn, Hn, Sd = a.W * a.sq - 1, H * a.sq - 1, a.sq
    assert all(unit_ok(q) for q in sqs)
    assert all(box_ok(D, Wn, Hn, Sd, q) for q in sqs), 'box'
    nfar = nsep = 0
    for ii in range(n):
        for jj in range(ii + 1, n):
            r = pair_ok(D, sqs[ii], sqs[jj])
            assert r is not None, ('pair fails', ii, jj)
            if r == 'far':
                nfar += 1
            else:
                nsep += 1
    # mirror of rowOK with the X cutoff: count pair tests actually done
    work = 0
    for ii in range(n):
        q = sqs[ii]
        for jj in range(ii + 1, n):
            r = sqs[jj]
            work += 1
            if q[0] <= r[0] and 2 * D * D < (r[0] - q[0]) ** 2:
                break
            assert pair_ok(D, q, r) is not None
    # chunk by a uniform head count k
    total = work
    k = max(1, round(n * a.pairs / total)) if total > a.pairs else n
    m = -(-n // k)
    sha = hashlib.sha256(open(a.cert, 'rb').read()).hexdigest()
    ddir = os.path.join(ROOT, 'Sqlean', 'Data')
    os.makedirs(os.path.join(ddir, a.name), exist_ok=True)
    ns = 'UnitSquarePacking.Data.%s' % a.name
    with open(os.path.join(ddir, a.name + '.lean'), 'w') as f:
        f.write('import Sqlean.CheckCore\n\n')
        f.write('/-! Generated by `scripts/gen_cert.py` from `%s`\n(sha256 %s).\n' % (os.path.basename(a.cert), sha))
        f.write('%d squares; box `[0, %d/%d] x [0, %d/%d]`. -/\n\n' % (n, Wn, Sd, Hn, Sd))
        f.write('namespace %s\n\nopen UnitSquarePacking.Cert\n\n' % ns)
        f.write('def D : Int := %d\ndef Wn : Int := %d\ndef Hn : Int := %d\ndef Sd : Int := %d\n' % (D, Wn, Hn, Sd))
        
        f.write('set_option maxRecDepth 100000 in\ndef L : List Sq := [\n')
        f.write(',\n'.join('  ⟨%s, %s, %s, %s, %s⟩' % tuple(lean_int(v) for v in q) for q in sqs))
        f.write(']\n\nend %s\n' % ns)
    # chunk files: one theorem per chunk, literal sizes (the kernel is much slower on `k * i`
    # with `k` a constant than on numerals)
    for old in os.listdir(os.path.join(ddir, a.name)):
        if old.startswith('Chk') and old.endswith('.lean'):
            os.remove(os.path.join(ddir, a.name, old))
    files = []
    chunks = list(range(m))
    for fi in range(0, m, a.per_file):
        fname = 'Chk%d' % (fi // a.per_file)
        files.append(fname)
        with open(os.path.join(ddir, a.name, fname + '.lean'), 'w') as f:
            f.write('import Sqlean.Data.%s\n\nnamespace %s\n\nopen UnitSquarePacking.Cert\n\n' % (a.name, ns))
            if fi == 0:
                f.write('theorem unit_ok : L.all unitOK = true := by decide +kernel\n\n')
                f.write('theorem box_ok : L.all (boxOK D Wn Hn Sd) = true := by decide +kernel\n\n')
                f.write('theorem len_eq : L.length = %d := by decide +kernel\n\n' % n)
                f.write('theorem sorted_ok : sortedX L = true := by decide +kernel\n\n')
            for c in chunks[fi:fi + a.per_file]:
                f.write('theorem chunk_%d : headsOK D %d (L.drop (%d * %d)) = true := by decide +kernel\n\n' % (c, k, k, c))
            f.write('end %s\n' % ns)
    # assembly (imports Mathlib through Sqlean.Check)
    os.makedirs(os.path.join(ROOT, 'Sqlean', 'Pieces'), exist_ok=True)
    with open(os.path.join(ROOT, 'Sqlean', 'Pieces', a.name + '.lean'), 'w') as f:
        f.write('import Sqlean.Check\n')
        for fname in files:
            f.write('import Sqlean.Data.%s.%s\n' % (a.name, fname))
        f.write('\n/-! `%s`: %d unit squares in `[0, %d - 1/%d] x [0, %d - 1/%d]`, from `%s`\n(sha256 %s). Generated by `scripts/gen_cert.py`. -/\n\n'
                % (a.name, n, a.W, a.sq, H, a.sq, os.path.basename(a.cert), sha))
        f.write('namespace %s\n\nopen UnitSquarePacking.Cert\n\n' % ns)
        f.write('theorem heads : headsOK D (%d * %d) L = true :=\n' % (k, m))
        f.write('  headsOK_chunks D L %d %d (fun i hi => by\n    interval_cases i\n' % (k, m))
        for c in chunks:
            f.write('    · exact chunk_%d\n' % c)
        f.write('  )\n\n')
        f.write('theorem packsR : PacksR %d ((%d : ℝ) - 1 / %d) ((%d : ℝ) - 1 / %d) := by\n' % (n, a.W, a.sq, H, a.sq))
        f.write('  have h := check_sound D Wn Hn Sd L (%d * %d) (by decide +kernel) (by decide +kernel) unit_ok box_ok\n' % (k, m))
        f.write('    sorted_ok (len_eq.trans_le (by decide)) heads\n')
        f.write('  rw [len_eq] at h\n')
        f.write('  have eW : ((Wn : ℤ) : ℝ) / ((Sd : ℤ) : ℝ) = (%d : ℝ) - 1 / %d := by simp only [Wn, Sd]; norm_num\n' % (a.W, a.sq))
        f.write('  have eH : ((Hn : ℤ) : ℝ) / ((Sd : ℤ) : ℝ) = (%d : ℝ) - 1 / %d := by simp only [Hn, Sd]; norm_num\n' % (H, a.sq))
        f.write('  rwa [eW, eH] at h\n\n')
        f.write('end %s\n' % ns)

    print('%s: n=%d D_bits=%d far=%d sep=%d (%.2f%% sep) row-tests=%d k=%d chunks=%d files=%d' % (
        a.name, n, D.bit_length(), nfar, nsep, 100.0 * nsep / max(1, nfar + nsep), work, k, m, len(files)))


if __name__ == '__main__':
    main()
