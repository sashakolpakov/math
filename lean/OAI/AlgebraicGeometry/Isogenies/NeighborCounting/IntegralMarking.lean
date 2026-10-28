import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Power
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.Labels

/-! # Integral Marking -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralMarking

noncomputable section

/-! The actual ordered full marking on a good quotient is determined by
its generic marking. Constant level sections extend uniquely over the DVR;
naturality then determines the marking on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralComparison OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Power.Construction

variable {R K : Type} [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {d N n : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of R))}

def constantLevelSection (α : A.FullLevel N)
    (c : Multiplicative (Fin (2 * d) → ZMod N)) :
    Over.mk (𝟙 (Spec (.of R))) ⟶ A.scheme :=
  (α.hom.app (.op (Over.mk (𝟙 _))) (LocallyConstant.const _ c)).val

/-- Generic transport of each constant label forces the complete integral
marking to be the quotient marking constructed by the prime-to-n isogeny. -/
theorem quotientLevel_eq_of_generic_marking
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (hnN : Nat.Coprime n N)
    (hkernel : ∀ (T : Over (Spec (.of R))) (a : T ⟶ A.scheme),
      a ≫ f.hom = 1 → a ^ n = 1)
    (α : A.FullLevel N) (β : B.FullLevel N)
    (hgeneric : ∀ c : Multiplicative (Fin (2 * d) → ZMod N),
      (Over.pullback (IntegralComparison.genericMap (R := R) (K := K))).map
          (constantLevelSection α c ≫ f.hom) =
        (Over.pullback (IntegralComparison.genericMap (R := R) (K := K))).map (constantLevelSection β c)) :
    AbelianScheme.FrobeniusKernel.Power.Construction.quotientLevel f hnN hkernel α = β := by
  apply AbelianModuli.ReferenceFamily.Frame.Labels.LevelCover.fullLevel_ext_on_constants
  intro c
  apply Subtype.ext
  have : Flat (Over.mk (𝟙 (Spec (.of R)))).hom := by
    change Flat (𝟙 (Spec (.of R)))
    infer_instance
  apply AbelianScheme.HomExtension.generic_fiber_map_injective (K := K)
    (Over.mk (𝟙 (Spec (.of R)))) B.scheme
  exact (congrArg (Over.pullback (IntegralComparison.genericMap (R := R) (K := K))).map
    (AbelianScheme.FrobeniusKernel.Power.Construction.quotientLevel_transports f hnN hkernel α _ (LocallyConstant.const _ c))).trans (hgeneric c)

/-- The resulting equality retains the complete ordered marking on arbitrary
tests, rather than only its geometric-point values. -/
theorem marking_transport_from_generic
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (hnN : Nat.Coprime n N)
    (hkernel : ∀ (T : Over (Spec (.of R))) (a : T ⟶ A.scheme),
      a ≫ f.hom = 1 → a ^ n = 1)
    (α : A.FullLevel N) (β : B.FullLevel N)
    (hgeneric : ∀ c : Multiplicative (Fin (2 * d) → ZMod N),
      (Over.pullback (IntegralComparison.genericMap (R := R) (K := K))).map
          (constantLevelSection α c ≫ f.hom) =
        (Over.pullback (IntegralComparison.genericMap (R := R) (K := K))).map (constantLevelSection β c))
    (T : Over (Spec (.of R)))
    (c : LocallyConstant T.left (Multiplicative (Fin (2 * d) → ZMod N))) :
    (α.hom.app (.op T) c).val ≫ f.hom = (β.hom.app (.op T) c).val := by
  exact (AbelianScheme.FrobeniusKernel.Power.Construction.quotientLevel_transports f hnN hkernel α (.op T) c).symm.trans
    (congrArg (fun γ : B.FullLevel N => (γ.hom.app (.op T) c).val)
      (quotientLevel_eq_of_generic_marking f hnN hkernel α β hgeneric))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralMarking
