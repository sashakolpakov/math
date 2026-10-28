import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResolutionOrientation
import OAI.NumberTheory.PadicHodge.IntegralComparison.LinearHomDualPurity

/-! # Linear Hom Oriented Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LinearHomOrientedPurity

noncomputable section

/-! Oriented purity for the original linear Hom complex, with an actual
rank-one target trivialization and exact determinant transition. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

universe u
variable (R : Type u) [CommRing R] {n : ℕ} (I : Ideal R)
  (s : Fin n → R) (hs : Koszul.OrientedTopCohomology.ideal R s = I)
  (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s))
  (P : ProjectiveResolution (ModuleCat.of R (R ⧸ I)))
  (N : ModuleCat.{u} R) (e : N ≅ ModuleCat.of R R)

def iso :
    (((((linearYoneda R (ModuleCat R)).obj N).mapHomologicalComplex
      (ComplexShape.down ℕ).symm).obj P.complex.op).homology n) ≅
      ModuleCat.of R (R ⧸ I) :=
  LinearHomDualPurity.targetHomologyIso R P.complex N e n ≪≫
    Koszul.ResolutionOrientation.purityIso R I s hs hreg P

variable (t : Fin n → R) (ht : Koszul.OrientedTopCohomology.ideal R t = I)
  (htreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn t))
  (A : Matrix (Fin n) (Fin n) R) (hA : ∀ i, s i = ∑ j, A i j * t j)

include hA in
theorem transition : (iso R I s hs hreg P N e).hom =
    (iso R I t ht htreg P N e).hom ≫
      ModuleCat.ofHom (A.det • (LinearMap.id : (R ⧸ I) →ₗ[R] (R ⧸ I))) := by
  dsimp only [iso, Iso.trans_hom]
  rw [Koszul.ResolutionOrientation.purity_transition R I s hs hreg t ht htreg A hA P,
    ← Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LinearHomOrientedPurity
