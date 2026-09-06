# Reviewed three-way mapping for the revised v6 snapshot

Paper commit: `f279b6fac180125dce81a82d824da971bb7ae715`. The proof/type/definition bindings are unchanged from the parent certification. Only source anchors and independently reviewed positive-dimension metadata were rebound. See `reviewed_crosswalk.json` for exact statements, types, definitions, source hashes and review details.

| Source item | New lines | Classification | Literal coverage |
|---|---:|---|---|
| thm:main | 109–122 | WRAPPER_ONLY | PASS |
| lem:transfer | 418–432 | EXACT_REUSE | PASS |
| prop:trace | 672–683 | EXACT_REUSE | PASS |
| cor:bernoulli | 699–712 | EXACT_REUSE | PASS |
| lem:graph | 976–985 | WRAPPER_ONLY | PASS |
| lem:cumulant-identities | 1140–1172 | NEW_FORMALIZATION | PASS |
| lem:cumulants | 1379–1392 | EXACT_REUSE | PASS |
| lem:count | 1799–1807 | EXACT_REUSE | PASS |
| lem:binary-constraints | 2307–2323 | WRAPPER_ONLY | PASS |
| prop:entry-contribution | 2433–2451 | WRAPPER_ONLY | PASS |
| lem:sampling | 2740–2768 | NEW_FORMALIZATION | PASS |
| lem:small | 2888–2898 | EXACT_REUSE | PASS |
| I-V6-01 | 85–108 | EXACT_REUSE | PASS |
| I-V6-02 | 124–139 | WRAPPER_ONLY | PASS |
| I-V6-03 | 384–411 | WRAPPER_ONLY | PASS |
| I-V6-04 | 443–456 | EXACT_REUSE | PASS |
| I-V6-05 | 458–532 | EXACT_REUSE | PASS |
| I-V6-06 | 534–560 | EXACT_REUSE | PASS |
| I-V6-07 | 562–630 | EXACT_REUSE | PASS |
| I-V6-08 | 716–776 | EXACT_REUSE | PASS |
| I-V6-09 | 922–930 | WRAPPER_ONLY | PASS |
| I-V6-10 | 931–937 | NEW_FORMALIZATION | PASS |
| I-V6-11 | 939–971 | EXACT_REUSE | PASS |
| I-V6-12 | 1001–1012 | EXACT_REUSE | PASS |
| I-V6-13 | 1014–1065 | WRAPPER_ONLY | PASS |
| I-V6-14 | 1195–1234 | NEW_FORMALIZATION | PASS |
| I-V6-15 | 1236–1322 | NEW_FORMALIZATION | PASS |
| I-V6-16 | 1324–1354 | NEW_FORMALIZATION | PASS |
| I-V6-17 | 1400–1416 | EXACT_REUSE | PASS |
| I-V6-18 | 1418–1465 | EXACT_REUSE | PASS |
| I-V6-19 | 1467–1499 | EXACT_REUSE | PASS |
| I-V6-20 | 1501–1534 | EXACT_REUSE | PASS |
| I-V6-21 | 1536–1585 | EXACT_REUSE | PASS |
| I-V6-22 | 1587–1621 | EXACT_REUSE | PASS |
| I-V6-23 | 1657–1675 | WRAPPER_ONLY | PASS |
| I-V6-24 | 1677–1711 | WRAPPER_ONLY | PASS |
| I-V6-25 | 1713–1739 | EXACT_REUSE | PASS |
| I-V6-26 | 1740–1754 | EXACT_REUSE | PASS |
| I-V6-27 | 1815–1895 | EXACT_REUSE | PASS |
| I-V6-28 | 1897–1931 | EXACT_REUSE | PASS |
| I-V6-29 | 1957–2056 | EXACT_REUSE | PASS |
| I-V6-30 | 2058–2134 | EXACT_REUSE | PASS |
| I-V6-31 | 2246–2276 | EXACT_REUSE | PASS |
| I-V6-32 | 2324–2347 | WRAPPER_ONLY | PASS |
| I-V6-33 | 2349–2360 | WRAPPER_ONLY | PASS |
| I-V6-34 | 2362–2400 | EXACT_REUSE | PASS |
| I-V6-35 | 2459–2479 | EXACT_REUSE | PASS |
| I-V6-36 | 2481–2507 | EXACT_REUSE | PASS |
| I-V6-37 | 2509–2553 | EXACT_REUSE | PASS |
| I-V6-38 | 2555–2563 | WRAPPER_ONLY | PASS |
| I-V6-39 | 2565–2594 | WRAPPER_ONLY | PASS |
| I-V6-40 | 2612–2658 | WRAPPER_ONLY | PASS |
| I-V6-41 | 2660–2710 | EXACT_REUSE | PASS |
| I-V6-42 | 2771–2790 | NEW_FORMALIZATION | PASS |
| I-V6-43 | 2791–2812 | EXACT_REUSE | PASS |
| I-V6-44 | 2814–2851 | EXACT_REUSE | PASS |
| I-V6-45 | 2853–2874 | NEW_FORMALIZATION | PASS |
| I-V6-46 | 2900–2942 | EXACT_REUSE | PASS |
| I-V6-47 | 2944–2987 | EXACT_REUSE | PASS |
| I-V6-48 | 2989–3003 | EXACT_REUSE | PASS |
| I-V6-49 | 3023–3053 | EXACT_REUSE | PASS |
| I-V6-50 | 3055–3110 | EXACT_REUSE | PASS |
| def:graph-contraction | 849–873 | WRAPPER_ONLY | definition mapped |
| def:boundary-matrix | 891–909 | WRAPPER_ONLY | definition mapped |
| def:input-output | 912–918 | WRAPPER_ONLY | definition mapped |
| def:joint-cumulant | 1081–1099 | NEW_FORMALIZATION | definition mapped |
| def:partition-join | 1122–1134 | EXACT_REUSE | definition mapped |
| def:equality-class | 1774–1786 | EXACT_REUSE | definition mapped |
| def:binary-constraint | 2284–2299 | WRAPPER_ONLY | definition mapped |
| D-V6-08 | 85–107 | EXACT_REUSE | definition mapped |
| D-V6-09 | 107–107 | WRAPPER_ONLY | definition mapped |
| D-V6-10 | 377–379 | EXACT_REUSE | definition mapped |
| D-V6-11 | 384–413 | EXACT_REUSE | definition mapped |
| D-V6-12 | 667–671 | EXACT_REUSE | definition mapped |
| D-V6-13 | 930–937 | NEW_FORMALIZATION | definition mapped |
| D-V6-14 | 1112–1120 | EXACT_REUSE | definition mapped |
| D-V6-15 | 1406–1407 | EXACT_REUSE | definition mapped |
| D-V6-16 | 1442–1465 | EXACT_REUSE | definition mapped |
| D-V6-17 | 1538–1548 | EXACT_REUSE | definition mapped |
| D-V6-18 | 1657–1673 | EXACT_REUSE | definition mapped |
| D-V6-19 | 1677–1695 | EXACT_REUSE | definition mapped |
| D-V6-20 | 1713–1739 | EXACT_REUSE | definition mapped |
| D-V6-21 | 1815–1830 | EXACT_REUSE | definition mapped |
| D-V6-22 | 1832–1854 | EXACT_REUSE | definition mapped |
| D-V6-23 | 1909–1931 | WRAPPER_ONLY | definition mapped |
| D-V6-24 | 2058–2101 | WRAPPER_ONLY | definition mapped |
| D-V6-25 | 2263–2276 | WRAPPER_ONLY | definition mapped |
| D-V6-26 | 2418–2431 | WRAPPER_ONLY | definition mapped |
| D-V6-27 | 2481–2486 | WRAPPER_ONLY | definition mapped |
| D-V6-28 | 2520–2541 | EXACT_REUSE | definition mapped |
| D-V6-29 | 2733–2738 | EXACT_REUSE | definition mapped |
| D-V6-30 | 2743–2746 | NEW_FORMALIZATION | definition mapped |
| D-V6-31 | 2775–2780 | NEW_FORMALIZATION | definition mapped |
| D-V6-32 | 2901–2905 | EXACT_REUSE | definition mapped |
| D-V6-33 | 3013–3019 | EXACT_REUSE | definition mapped |
| D-V6-34 | 3055–3059 | EXACT_REUSE | definition mapped |
