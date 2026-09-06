# Readable frozen-v6 correspondence crosswalk

Reviewer `/root/v6_inventory`. This is a human-readable source/implementation map; actual final kernel, axiom and cold-build evidence remain separately required. Status below is semantic correspondence, never an automatic kernel PASS. Frozen scope is unchanged: 12 named results, 30 conjuncts, 50 interfaces, 34 definitions (7 named). Each source range and exact byte hash is retained in its named inventory; three_way_candidate_map.json retains A and B pointers. The current combined binding covers 189 actual theorem targets and 39 actual expected/primitive definitions; 33 reviewer-owned expected-type assignments compiled successfully. The general allowed-modification theorem is still open.

## Named statements

| C number / label | C lines / conjuncts | Actual proof route | Current correspondence |
|---|---|---|---|
| 1: `thm:main` | 109–122 / 3 | `main_universal_ose; PaperV6.fixed_frame_ose; squared-norm clients` | Exact universal width and fixed-frame interpretation; implementation reviewed; current actual-type binding checked |
| 2: `lem:transfer` | 418–432 / 2 | `two_projection_spectral_transfer` | Exact arbitrary real projections and delta; source/B type reviewed |
| 3: `prop:trace` | 672–683 / 1 | `signed_trace_proposition` | Exact signed expectation, K0 and hypotheses; source/B type reviewed |
| 4: `cor:bernoulli` | 699–712 / 1 | `bernoulli_coordinate_sampling_corollary` | Exact logarithmic p and two-sign/Bernoulli law |
| 5: `lem:graph` | 975–984 / 1 | `PaperV6.graph_rank` | Exact C transpose convention; graph rank body reviewed |
| 6: `lem:cumulant-identities` | 1139–1171 / 6 | `PaperV6.generalCumulantIdentities and its six components` | All six general probability-space statements; actual proofs reviewed |
| 7: `lem:cumulants` | 1378–1391 / 3 | `joint_entry_cumulant_lemma; centering interfaces` | Exact normalized entry cumulants, XOR and mean |
| 8: `lem:count` | 1798–1806 / 2 | `selector_equality_graph_count` | Both loop count and equality-count bound retained |
| 9: `lem:binary-constraints` | 2306–2322 / 5 | `PaperV6.binary_forbidden_pair; binary_count; binary_odd_incidence` | All three clauses, actual XOR rank and injective subset |
| 10: `prop:entry-contribution` | 2432–2450 / 3 | `PaperV6.entry_weighted_count; entry_absolute_contribution` | All d,h, exact weight and internal absolute finite sums |
| 11: `lem:sampling` | 2739–2767 / 1 | `PaperV6.general_sampling; finiteNoiseFailureLaw; general_sampling_joint` | Arbitrary X averaged and concrete independent realization proofs source-reviewed; current compiled expected assignment checked |
| 12: `lem:small` | 2887–2897 / 2 | `small_rank_second_moment` | Exact finite-population bound and selected width consequence |

## All frozen proof-strength interfaces

“B route reviewed” means the source was compared with the recorded baseline interface/type and source proof, together with the separately bounded baseline reverse audit. It does not assert this reviewer re-proved every transitive helper. Additive changes and nonliteral route boundaries are explicit.

| Interface | C lines | Source obligation | Route and qualification |
|---|---|---|---|
| I-V6-01 | 85–108 | Walsh orthogonality, transformed-frame orthonormality, and exact sampled Gram identity | I01/I02. B route reviewed; exact source assumptions remain controlling. |
| I-V6-02 | 124–139 | For each fixed frame, the spectral success event is equivalent to simultaneous squared-norm inequalities for all z∈R^r; universal width precedes frame; full sampling exact | NEW fixed-frame and quadratic-form bridge; I03. Additive FixedFrame proof derives the per-frame and simultaneous squared-norm interpretation. |
| I-V6-03 | 384–411 | Gram centering identity, cyclic power trace equality tr(XᵀWX)^j=tr(PW)^j, and need for zero first cumulants | I02/I15; trace cyclicity. B route reviewed; exact source assumptions remain controlling. |
| I-V6-04 | 443–456 | Compressed isometry identifies eigenvalues, each in [0,1], and error norm equals theta⁻¹max\|lambda−theta\| | I31; spectral norm interpretation. B route reviewed; exact source assumptions remain controlling. |
| I-V6-05 | 458–532 | Full finite two-projection decomposition, orthogonality of distinct pairs, endpoints lambda=0,1 and complement in ker P; at most r two-dimensional blocks | I31. B route reviewed; exact source assumptions remain controlling. |
| I-V6-06 | 534–560 | Centered 2×2 block polynomial z²−tz+a² with fixed product a² and t=lambda−delta−theta+2delta theta | I32. B route reviewed; exact source assumptions remain controlling. |
| I-V6-07 | 562–630 | Root power sums equal trace even for defective block; nonreal contribution≥−2a^(2p); spectral deviation produces block contribution>(theta eta/2)^(2p), including endpoints | I33/I34. B route reviewed; exact source assumptions remain controlling. |
| I-V6-08 | 716–776 | Taking expectations of compensated signed trace gives Bernoulli bound (K0^p+2r)(4r/(kappa eta²))^p and logarithmic-order probability arithmetic | bernoulli_coordinate_sampling_corollary_of_trace. B route reviewed; exact source assumptions remain controlling. |
| I-V6-09 | 921–929 | Input-output boundary operator norm at most product of edge norms in compatible rectangular spaces | I04 plus transpose/boundary bridge. GraphBridges proves transpose and input-output norm correspondence. |
| I-V6-10 | 930–936 | Every connected bridgeless finite graph may be modified to input-output form with any prescribed distinct boundary vertices | NEW_OR_EXTERNAL_SOURCE_INTERFACE; B I05 strictly narrower. FULL SOURCE SCOPE RETAINED: published Lemma16 independently verified. No literal allowed-modification history or full general operator-consequence kernel result yet; primitive ear selection and simple return paths are proved. |
| I-V6-11 | 938–970 | Allowed identity-edge splits and edge reversal/transposition preserve each fixed boundary entry and full sum; identity edges have norm 1 | GraphVertexSplit/GraphFiberSplit; stronger than scalar-only I05 conclusion. GraphModifications proves explicit fiber boundary equality, reversal, positive-dimensional identity norm and norm product. Arbitrary finite modification-history object is not encoded. |
| I-V6-12 | 1000–1011 | Connected positive-even graph is bridgeless; vertex weights absorb into norm≤1 loops preserving contraction and even degrees | I06; GraphWeightLoops. B route reviewed; exact source assumptions remain controlling. |
| I-V6-13 | 1013–1064 | Projection factorization and split insert two distinct r-dimensional boundary vertices preserving signed contraction including loop case, then \|1ᵀT1\|≤r | I07; GraphRankEdgeSplit; transpose bridge. B route reviewed; exact source assumptions remain controlling. |
| I-V6-14 | 1194–1233 | Formal logarithm squarefree coefficient is cumulant; exponential inverse gives moment identity | GENERAL algebraic coefficient interface. Written formal-log coefficients reviewed. General moment identity has alternative partition-cancellation proof; formal-series coefficient objects themselves are not formalized. |
| I-V6-15 | 1235–1321 | Expanding product cumulants groups by join; ordered partitions have j! orderings; Stirling coefficient sum is indicator(b=1) | I09 combinatorial cancellation plus general expectation bridge. General Product proof reindexes actual finite partition products and uses Stirling cancellation on arbitrary moment data. |
| I-V6-16 | 1323–1353 | Moment polynomial factorization under independent families yields mixed vanishing; deterministic argument vanishes at order≥2; symmetry law gives odd vanishing | GENERAL expectation/law interface. General Mixed/Multilinear/Shifts/Symmetry proofs retain arbitrary probability space and finite requisite moments. |
| I-V6-17 | 1399–1415 | Exact four-index projection entry expansion with both inner Walsh matrices normalized | I11. B route reviewed; exact source assumptions remain controlling. |
| I-V6-18 | 1417–1464 | Two-layer even occurrence partitions with connected join give exact cumulant sum; different blocks may share labels | ProductCumulant; joint_entry_cumulant_assembly. B route reviewed; exact source assumptions remain controlling. |
| I-V6-19 | 1466–1498 | Connected join gives connected positive-even occurrence graph with unrestricted signed contraction, rank-r projection edge and character vertex weights | I12. B route reviewed; exact source assumptions remain controlling. |
| I-V6-20 | 1500–1533 | Rademacher cumulant≤b^(2b); each layer coefficient≤(2q)^(4q); pair partition count≤(2q)^(4q) | I13. B route reviewed; exact source assumptions remain controlling. |
| I-V6-21 | 1535–1584 | Walsh modulation/translation identities preserve exact two-layer law for same fixed V; nonzero XOR separates by character sign | I14. B route reviewed; exact source assumptions remain controlling. |
| I-V6-22 | 1586–1620 | Conditional sign averages yield E P=delta I; centering gives zero all entries and unchanged cumulants order≥2 | I15. B route reviewed; exact source assumptions remain controlling. |
| I-V6-23 | 1656–1674 | Exact signed trace expansion separates sign and selector expectations | TraceCyclicExpansion; SignedTraceExpansion. B route reviewed; exact source assumptions remain controlling. |
| I-V6-24 | 1676–1710 | Regrouping words by exact equality partition is bijection to injective block labels; singleton selector blocks vanish | signBernoulliExpectation_trace_eq_partition_cumulant_sum. B route reviewed; exact source assumptions remain controlling. |
| I-V6-25 | 1712–1738 | Quotient graph connected, degrees 2m_u≥4, total excess 4s, and s+t≤p | I16. B route reviewed; exact source assumptions remain controlling. |
| I-V6-26 | 1739–1753 | Centered Bernoulli moment formula and \|Ew^b\|≤theta give selector product≤theta^v | I17. B route reviewed; exact source assumptions remain controlling. |
| I-V6-27 | 1814–1894 | Marked vertices/degree budgets; complete local degree-four classification; terminal paths reach B without merging; B-empty graph classification | I18/I19. B route reviewed; exact source assumptions remain controlling. |
| I-V6-28 | 1896–1930 | Maximal internal doubled chains contract with returning/parallel port identity and zero length allowed; no isolated internal cycle when B nonempty | ContractedCore* topology and realization. B route reviewed; exact source assumptions remain controlling. |
| I-V6-29 | 1956–2055 | Retained q≤8a,D≤36a,q≤p,D≤4p; degree/edge/port/length encoding ≤L^(72a); deterministic expansion surjects all original graphs | I20; ContractedCoreEncodingClosure. B route reviewed; exact source assumptions remain controlling. |
| I-V6-30 | 2057–2133 | Euler local pairings≤3^p L^(2s); starting edge≤4p; decoding recovers exact numbered partition without extra vertex permutation; a=0 count≤8p3^p | I21. B route reviewed; exact source assumptions remain controlling. |
| I-V6-31 | 2245–2275 | Entry moments expand by rho distinct from equality pi; singleton entry blocks including loops vanish; b=p−d with 0≤d≤p−1 | SignedTraceEntryCumulant. B route reviewed; exact source assumptions remain controlling. |
| I-V6-32 | 2323–2346 | Forbidden pair XOR contradicts injectivity; surviving pair types are parallel, disjoint, two loops; nonzero pair rows have weight four | I23; PointwiseVanishing. BinaryBridges explicitly matches forbidden/surviving cases and paper block XOR sums. |
| I-V6-33 | 2348–2359 | Binary-coordinate kernels give exactly n^(v−h) unrestricted labelings; injective subset count bound | entryXorConstraintSolutionCount. BinaryBridges calls the actual full constraint-rank kernel count; injective count is an inclusion bound. |
| I-V6-34 | 2361–2399 | Large occurrences≤6d/touched≤12d; odd vertices outside large blocks lie in support of disjoint pair rows; basis supports union≤4h | I24. B weight-four row support may strictly contain source disjoint-pair support; use subset, never definitional equality. Odd bound is exposed by BinaryBridges. |
| I-V6-35 | 2458–2478 | Large-block selection/partition count≤L^(12d), weight≤L^(72d), pair weights≤K2^p including d=0 | I25 plus actual weighted aggregation. B route reviewed; exact source assumptions remain controlling. |
| I-V6-36 | 2480–2506 | Disjoint support choices≤L^(4h), available occurrences≤8h+2s, subset/pair count≤L^(8h+2s) | I26. B route reviewed; exact source assumptions remain controlling. |
| I-V6-37 | 2508–2552 | Loop pairing≤L^(2t+6s+1); parallel pairing≤3^p L^s using remaining multiplicities and original degree excess | I27; PairingParallelBound. B route reviewed; exact source assumptions remain controlling. |
| I-V6-38 | 2554–2562 | All exact admissible partitions covered by product of counts and exact c(rho) weighting | I28. EntryBridges removes the old d-range restriction through a proved empty-class alternative. |
| I-V6-39 | 2564–2593 | Block cumulant bound scales as (2q)^(12q)r n^(−q), products as c(rho)r^(p−d)n^(−2p); XOR supports dimension identity | I29; centeredProjection_partitionCumulantProduct_bound. EntryBridges proves the literal fixed-class internal-absolute contribution and signed-power factor. |
| I-V6-40 | 2611–2657 | Triangle inequalities and equality count give finite trace majorization with full feasible parameter ranges | SignedTraceExpansion; signedTrace_master_geometric_bound. B route reviewed; exact source assumptions remain controlling. |
| I-V6-41 | 2659–2709 | Geometric t sum≤2L^(912d+304h), triple sum≤8,128pL≤64^p give K0=576K2 | I30; TraceGeometric. B route reviewed; exact source assumptions remain controlling. |
| I-V6-42 | 2770–2789 | Independent continuous uniforms give uniform k-smallest subset, correct Bernoulli marginals and count-bracketing inclusions | WRITTEN_CONTINUOUS_COUPLING; B finite alternative. Written continuous uniform order-statistic construction reviewed. SamplingPointwise finite common-order coupling is an alternative proof, not the same continuous object. |
| I-V6-43 | 2790–2811 | Loewner sandwich plus marginal Gram successes imply fixed Gram eigenvalues between (1±epsilon/4)^2⊂[1−epsilon,1+epsilon] | I36; SamplingArithmetic. B route reviewed; exact source assumptions remain controlling. |
| I-V6-44 | 2813–2850 | Two binomial tail bounds derived by exponential Markov and explicit mgf/factorial estimates | I37; BinomialTail. B route reviewed; exact source assumptions remain controlling. |
| I-V6-45 | 2852–2873 | Count tail union bound plus two marginal Gram failures gives 2gamma+2exp(−epsilon²k/48) | I35-I37 plus general averaging bridge. SamplingPointwise + arbitrary-space integration reviewed; concrete independent-law client now source-reviewed; current compiled expected assignment checked. |
| I-V6-46 | 2899–2941 | Fixed-size inclusion probabilities, conditional mean I and exact finite-population Frobenius second moment | I38. B route reviewed; exact source assumptions remain controlling. |
| I-V6-47 | 2943–2986 | Conditional row Rademacher law and exact vector fourth moment r²+2r−2sum rownorm⁴; row average bound | I39. B route reviewed; exact source assumptions remain controlling. |
| I-V6-48 | 2988–3002 | Average finite-population identity, operator norm domination and Markov imply small-rank width success | I40; small_rank_second_moment. B route reviewed; exact source assumptions remain controlling. |
| I-V6-49 | 3022–3052 | Threshold R0=2^20000 ensures logarithmic p rank condition using monotonic f | I41. B route reviewed; exact source assumptions remain controlling. |
| I-V6-50 | 3054–3109 | Three deterministic width branches, both Bernoulli densities and effective widths, final probability and universal width arithmetic | I42; main_universal_ose. B route reviewed; exact source assumptions remain controlling. |

## Definitions and representation bridges

| Definition | C lines | Meaning / actual representation | Qualification |
|---|---|---|---|
| def:graph-contraction | 849–872 | Signed unrestricted contraction; paperGraphContraction; graph_orientation | Source definition read; occurrence indices and ambient conventions retained. |
| def:boundary-matrix | 890–908 | Fixed boundary-entry matrix; paperBoundaryMatrix; graph_boundary | Source definition read; occurrence indices and ambient conventions retained. |
| def:input-output | 911–917 | Acyclic unique input/output; PaperInputOutput; paperInputOutput_iff | Source definition read; occurrence indices and ambient conventions retained. |
| def:joint-cumulant | 1080–1098 | Finite-moment real joint cumulant; measureJointCumulant; finite B jointCumulant specialization | Source definition read; occurrence indices and ambient conventions retained. |
| def:partition-join | 1121–1133 | Join connectedness of occurrence partitions; ProductPartitionConnected, proved partition equivalences | Source definition read; occurrence indices and ambient conventions retained. |
| def:equality-class | 1773–1785 | Exact selector equality class; SelectorEqualityData | Source definition read; occurrence indices and ambient conventions retained. |
| def:binary-constraint | 2283–2298 | Occurrence XOR constraint matrix over F2; entryConstraintMatrix; PaperXorConstraints; binary_count | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-08 | 85–107 | Exact normalized real Walsh model, sign diagonals, uniform fixed subset, sample matrix, SRHT, transformed frame/projection, delta;  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-09 | 107–107 | Euclidean operator norm convention;  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-10 | 377–379 | Natural logarithm, binary logarithm, Frobenius norm;  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-11 | 384–413 | Independent Bernoulli E, centered W,R,A;  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-12 | 667–671 | kappa=n theta, K2=4^24,K0=576K2;  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-13 | 929–936 | Bridge deletion convention and general bridgeless graph;  | General edge-deletion definition approved separately; literal general conversion history remains open. |
| D-V6-14 | 1111–1119 | Finite occurrence positions with repetition, prescribed groups tau, product variables;  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-15 | 1405–1406 | P0=VVᵀ, characters chi, signs xi;  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-16 | 1441–1464 | Rademacher order cumulant and unrestricted S_alpha,beta graph sums;  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-17 | 1537–1547 | Translation T_s and modulation C_s;  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-18 | 1656–1672 | Cyclic 2p trace word and selector w_i;  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-19 | 1676–1694 | Exact equality partition pi, m_u,v=p−s;  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-20 | 1712–1738 | Quotient edges, loops ell, odd-incident vertex count t;  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-21 | 1814–1829 | Marked vertices B and marked degree D_B;  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-22 | 1831–1853 | Three unmarked degree-four vertex types;  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-23 | 1908–1930 | Retained graph, distinguished half-edge ports, returning/parallel links and lengths;  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-24 | 2057–2100 | Euler transition system and alternating edge/local pairings;  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-25 | 2262–2275 | Entry occurrence partition rho and b=p−d;  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-26 | 2417–2430 | Exact R_dh(pi) and weight c(rho);  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-27 | 2480–2485 | Disjoint-pair support union U;  | B support is a safe superset, not identical to source U; no exact-definition claim. |
| D-V6-28 | 2519–2540 | Remaining parallel multiplicities a_e and positive part (x)+;  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-29 | 2732–2737 | Coordinate projection E_B and Loewner order;  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-30 | 2742–2745 | alpha and theta± coupling parameters;  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-31 | 2774–2779 | Continuous uniform order statistic coupling J,B±,N±;  | Continuous source object reviewed only; finite formal coupling is an alternative representation for the required law. |
| D-V6-32 | 2900–2904 | Rows x_iᵀ and normalized fixed Gram G;  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-33 | 3012–3018 | Universal constants R0 and C;  | Source definition read; occurrence indices and ambient conventions retained. |
| D-V6-34 | 3054–3058 | Large-rank chosen width k0;  | Source definition read; occurrence indices and ambient conventions retained. |

No inventory entry was dropped or rewritten to fit an existing theorem. A kernel-proved consequence and the literal source proof route remain separate statuses.

Current interface accounting: 47/50 literal source interfaces; 49/50 required consequences when the independently reviewed alternative proofs for I-V6-14 and I-V6-42 are counted. I-V6-10 remains open. I-V6-11 per-operation preservation is covered and is not subtracted a second time for pending history integration.
