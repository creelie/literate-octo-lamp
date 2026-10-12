# verify_lemmas.jl -- the steps of the proof, on every binary circular word of length n <= NMAX.
#
# A word is a vector of letters 1 (= a) and 0 (= b), read cyclically. For 1 <= m <= n-1 the
# window of half-length m at i is x[i], ..., x[i+2m-1] (indices mod n); it is an abelian square
# if both halves hold the same number of a's. Q_m is the set of pairs (l, k): l the last letter of
# the left half, k the number of l's in it. S_m (2m <= n) is the set of distinct abelian squares
# of length 2m, and D = sum |S_m|. The column C_l(k) is the set of m with (l, k) in Q_m.
#
# Checked for every word:
#   Lemma 2.1  |Q_m| <= |S_m| for 2m <= n
#   Lemma 2.2  (l, k) in Q_m  =>  (l, t_l - k) in Q_{n-m}
#   Lemma 2.3  C_l(k) is nonempty for 1 <= k < t_l
#   Theorem 2.4  D >= floor((n-1)/2)
#   Theorem 3.1  if l is tight (each column has one element) and the word is rigid (|S_m| = |Q_m|
#                for 2m <= n), then the word is a conjugate of l^t lbar^(n-t) with t odd or t = n,
#                or n = 2t and the word is a conjugate of (l lbar)^(n/2)
#   Lemma 4.2  in a conjugate of l^alpha lbar^(2h), alpha >= 3, the column C_lbar(h) contains
#                h, h+1 and n-h
#   Theorem 4.3  D = floor((n-1)/2) exactly on the family of the paper

const NMAX = 16

letter(w, i, n) = (w >> (mod(i, n))) & 1

function count_ones(w, i, len, n)
    c = 0
    for t in 0:len-1
        c += letter(w, i + t, n)
    end
    c
end

# Q[m] as a Set of (l, k), and S[m] as a Set of window encodings (2m <= n)
function signatures(w, n)
    Q = [Set{Tuple{Int,Int}}() for _ in 1:max(n - 1, 1)]
    S = [Set{UInt64}() for _ in 1:max(n ÷ 2, 1)]
    for m in 1:n-1, i in 0:n-1
        left = count_ones(w, i, m, n)
        right = count_ones(w, i + m, m, n)
        left == right || continue
        l = letter(w, i + m - 1, n)
        k = l == 1 ? left : m - left
        push!(Q[m], (l, k))
        if 2m <= n
            code = UInt64(1)
            for t in 0:2m-1
                code = (code << 1) | UInt64(letter(w, i + t, n))
            end
            push!(S[m], code)
        end
    end
    Q, S
end

rot(w, r, n) = ((w >> r) | (w << (n - r))) & ((1 << n) - 1)
conjugates(w, n) = Set(rot(w, r, n) for r in 0:n-1)
compl(w, n) = (~w) & ((1 << n) - 1)
block(l, alpha, n) = l == 1 ? (1 << alpha) - 1 : compl((1 << alpha) - 1, n)   # l^alpha lbar^(n-alpha)
alternating(l, n) = (a = sum(1 << i for i in 0:2:n-1); l == 1 ? a : compl(a, n))

function family(n)
    F = Set{Int}()
    for l in (0, 1)
        if isodd(n)
            union!(F, conjugates(block(l, n, n), n), conjugates(block(l, n - 1, n), n))
        else
            for k in 1:2:n-1
                union!(F, conjugates(block(l, k, n), n))
            end
            n % 4 == 2 && union!(F, conjugates(alternating(l, n), n))
        end
    end
    F
end

function main()
    ok = true
    for n in 1:NMAX
        fam = family(n)
        ntight = 0
        nfail = 0
        for w in 0:(1 << n) - 1
            Q, S = signatures(w, n)
            t = Dict(1 => count_ones(w, 0, n, n), 0 => n - count_ones(w, 0, n, n))
            D = n >= 2 ? sum(length(S[m]) for m in 1:n÷2) : 0
            # Lemma 2.1
            all(length(Q[m]) <= length(S[m]) for m in 1:n÷2) || (nfail += 1)
            # Lemma 2.2
            for m in 1:n-1, (l, k) in Q[m]
                (l, t[l] - k) in Q[n - m] || (nfail += 1)
            end
            # columns
            col(l, k) = [m for m in 1:n-1 if (l, k) in Q[m]]
            for l in (0, 1), k in 1:t[l]-1
                isempty(col(l, k)) && (nfail += 1)          # Lemma 2.3
            end
            # Theorem 2.4
            D >= (n - 1) ÷ 2 || (nfail += 1)
            # Theorem 3.1
            rigid = all(length(Q[m]) == length(S[m]) for m in 1:n÷2)
            for l in (0, 1)
                t[l] >= 1 || continue
                tight = all(length(col(l, k)) <= 1 for k in 1:t[l]-1)
                (tight && rigid) || continue
                ntight += 1
                a = t[l]
                good = ((isodd(a) || a == n) && w in conjugates(block(l, a, n), n)) ||
                       (n == 2a && w in conjugates(alternating(l, n), n))
                good || (nfail += 1)
            end
            # Lemma 4.2
            for l in (0, 1), alpha in 3:n-2
                beta = n - alpha
                iseven(beta) || continue
                h = beta ÷ 2
                if w in conjugates(block(l, alpha, n), n)
                    c = col(1 - l, h)
                    (h in c && (h + 1) in c && (n - h) in c) || (nfail += 1)
                end
            end
            # Theorem 4.3
            ((D == (n - 1) ÷ 2) == (w in fam)) || (nfail += 1)
        end
        println("n=$(lpad(n, 2))  words=$(lpad(1 << n, 6))  tight-and-rigid cases=$(lpad(ntight, 5))  ",
                nfail == 0 ? "ok" : "FAIL ($nfail)")
        ok &= nfail == 0
    end
    println(ok ? "ALL OK" : "SOME CHECKS FAILED")
    ok
end

exit(main() ? 0 : 1)
