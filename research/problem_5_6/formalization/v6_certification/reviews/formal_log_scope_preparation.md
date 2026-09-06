# Formal-log scope preparation and frozen source binding

Independent reviewer `/root/baseline_audit`; source-interface review of C I-V6-14. The original pre-proof expected approval belongs to `/root/v6_inventory` in `formal_log_expected_review.md`; this later review read frozen C lines 1194–1233 and the expected definitions before reading implementations. It does not backdate its own review or author any coefficient proof.

Frozen C commit: `4551d08f3732a3ca06c2f576794e1d75790e1972`. Exact interface context SHA256: `c6fb4f8e1dcb925e0810ad2a55904ed519510e417ed7d0de0fc8eeea2c90caec`.

## Six reviewed source hashes

| File | SHA256 |
|---|---|
| `FormalLogExpected.lean` | `695382ecee0656a1388765fbe8e5a5a5c987d5272415a2512f5b259b9e068814` |
| `FormalLogBasic.lean` | `b586eee3e034990038dca5cabfbc9e38386f54d549e3f152aadb65c9de637976` |
| `FormalLogPartitions.lean` | `40e27cf813f551c8e6ecae5a29f851fa9e2c8c89c8d8d83eb67da8a6ba00a37a` |
| `FormalLogPowers.lean` | `238c1a36a93f8c5ebcfa041efcab2a9189943f916c130fcacb09112d6f3dcdce` |
| `FormalLogCoefficients.lean` | `67714ee015e51a541d375def0c60f4ff8ed8c099579f4d3a647b907152a45502` |
| `FormalLogInverse.lean` | `f40c1fb3dbd4ef982f37ef136a4fc0019d6db8f56fdf2d082c8dd2eeaf76438c` |

## Five exported expected propositions

| Frozen proposition | Existing theorem | Exact scope |
|---|---|---|
| `SquarefreePowerCoefficientExpected` | `squarefreePowerCoefficient` | Arbitrary real coefficient function f with f(empty)=0; every finite occurrence set S and every j, including j=0; actual recursive convolution power equals j! times its j-block partition sum. |
| `SquarefreePowerTruncationExpected` | `squarefreePowerTruncation` | For the same arbitrary coefficient function with zero empty coefficient, powers above card(S) have coefficient zero, including S=empty. |
| `FormalLogMomentCoefficientExpected` | `formalLogMomentCoefficient` | For arbitrary real random variables on a probability space with finite requisite joint moments, every nonempty occurrence subset S has squarefree log coefficient equal to the joint cumulant on the subtype S. |
| `FormalExpLogMomentExpected` | `formalExpLogMoment` | For the same probability moments, squarefreeExp(squarefreeLog(moment)) recovers the actual integral moment coefficient for every S, including empty. |
| `FormalLogEmptyCoefficientsExpected` | `formalLogEmptyCoefficients` | Probability normalization implies moment(empty)=1, log moment(empty)=0 and exp(log moment)(empty)=1; no Fintype on the whole occurrence type or moment hypothesis is needed for this endpoint. |

The aggregate export is exactly:

```lean
theorem formalLogMomentInterface :
    SquarefreePowerCoefficientExpected ∧ SquarefreePowerTruncationExpected ∧
    FormalLogMomentCoefficientExpected ∧ FormalExpLogMomentExpected ∧
    FormalLogEmptyCoefficientsExpected
```

Primitive definitions are actual coefficients: squarefreeUnit is the empty monomial unit; squarefreeMul sums f(T)g(S\T) over subsets T of S; squarefreePow recursively multiplies these coefficients; squarefreeLog uses the coefficients (-1)^(j-1)/j of powers of m-unit up to card(S); squarefreeExp uses actual powers divided by j!; squarefreeMoment is the integral of the indexed finite product. None is defined to be the desired partition sum, cumulant or inverse coefficient.

The squarefree quotient is a coefficient representation of the source formal series: a nonsquarefree monomial cannot contribute to a squarefree monomial under multiplication. Log interpretation requires m(empty)=1; exp interpretation in this finite truncation requires f(empty)=0. The applications prove these conditions. This review does not claim an unrestricted infinite MvPowerSeries object or a general analytic exp/log theorem. It covers the precise squarefree coefficient assertions used by C.

`ExpectedFormalLogChecks.lean` contains five explicit expanded type assignments and the aggregate assignment. Its role is a separate reviewer-owned client check; the controller builds it serially. Its creation is not a compilation receipt.
