import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.EndomorphismBridge
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Parameter
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RepresentedSubfunctor

/-! # Bounded Endomorphism Tuples -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.BoundedEndomorphismTuples

noncomputable section

/-! The full Presentations input constructs bounded tuples of actual group
endomorphisms, with their universal maps and exact arbitrary-test classifier. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.EndomorphismBridge.EndomorphismFamilies
variable {S : Scheme.{0}} {g n : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

def e34GroupEndTuple (T : Over S) (r : Fin n → Finite.Actions.GroupEndRing (A.pullback T.hom)) :
    (HilbertScheme.Presentations.Endomorphisms.Core.endomorphismTuples A.scheme n).obj (op T) := fun i => EndomorphismBridge.EndomorphismFamilies.e34EndomorphismEquiv A T (r i)

theorem e34GroupEndTuple_injective (T : Over S) : Function.Injective (e34GroupEndTuple A (n := n) T) := by
  intro r q h
  funext i
  exact (EndomorphismBridge.EndomorphismFamilies.e34EndomorphismEquiv A T).injective (congrFun h i)

theorem e34GroupEndTuple_natural {T U : Over S} (f : T ⟶ U)
    (r : Fin n → Finite.Actions.GroupEndRing (A.pullback U.hom)) :
    (HilbertScheme.Presentations.Endomorphisms.Core.endomorphismTuples A.scheme n).map f.op (e34GroupEndTuple A U r) =
      e34GroupEndTuple A T (fun i => EndomorphismFamiliesId.EndomorphismFamilies.restrict A f (r i)) := by
  funext i
  apply Subtype.ext
  exact (EndomorphismHom.EndomorphismFamilies.relativeHom_restrict A f (r i)).symm

theorem exists_e34_bounded_endomorphism_tuples [IsLocallyNoetherian S]
    (hPresentations : Hilbert.EndomorphismEquationsInput.{0}) (BA : HilbertScheme.Presentations.Has.Core.ProjectivePresentation A.scheme)
    (P : Fin n → Polynomial ℚ) :
    ∃ (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A.scheme ⨯ A.scheme)) (Z : Over S),
      HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation BA BA B ∧ LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧
      IsSeparated Z.hom ∧ ∃ rZ : Fin n → Finite.Actions.GroupEndRing (A.pullback Z.hom),
        ∀ (T : Over S) (r : Fin n → Finite.Actions.GroupEndRing (A.pullback T.hom)),
          HilbertScheme.Presentations.Has.Core.HasGraphPolynomials A.scheme A.scheme n B P
            ((HilbertScheme.Presentations.Endomorphisms.Core.forgetGroupLaw A.scheme n).app (op T) (e34GroupEndTuple A T r)) ↔
            ∃! f : T ⟶ Z, ∀ i, EndomorphismFamiliesId.EndomorphismFamilies.restrict A f (rZ i) = r i := by
  obtain ⟨B, L, hB, ⟨M⟩⟩ := hPresentations A.scheme BA n P []
  obtain ⟨hft, hqc, hsep⟩ := Parameter.e34SolutionScheme_finiteType_separated A.scheme M
  let F := HilbertScheme.Presentations.Endomorphisms.Core.endomorphismTuples A.scheme n
  let Z := M.solutionScheme
  let u := RepresentedSubfunctor.representedSubfunctorUniversal F M.solutionLocus Z M.solutionEquivalence
  let rZ (i : Fin n) := (EndomorphismBridge.EndomorphismFamilies.e34EndomorphismEquiv A Z).symm (u i)
  have hu : e34GroupEndTuple A Z rZ = u := by
    funext i
    exact (EndomorphismBridge.EndomorphismFamilies.e34EndomorphismEquiv A Z).apply_symm_apply (u i)
  refine ⟨B, Z, hB, hft, hqc, hsep, rZ, fun T r => ?_⟩
  have hm : e34GroupEndTuple A T r ∈ M.solutionLocus.obj (op T) ↔
      HilbertScheme.Presentations.Has.Core.HasGraphPolynomials A.scheme A.scheme n B P
        ((HilbertScheme.Presentations.Endomorphisms.Core.forgetGroupLaw A.scheme n).app (op T) (e34GroupEndTuple A T r)) := by
    rw [M.solution_mem]
    simp only [HilbertScheme.Presentations.Endomorphisms.Core.SatisfiesEquations, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  rw [← hm, RepresentedSubfunctor.representedSubfunctorUniversal_classifies F M.solutionLocus Z M.solutionEquivalence]
  have hf (f : T ⟶ Z) : F.map f.op u = e34GroupEndTuple A T r ↔
      ∀ i, EndomorphismFamiliesId.EndomorphismFamilies.restrict A f (rZ i) = r i := by
    rw [← hu, e34GroupEndTuple_natural]
    exact ⟨fun h i => congrFun (e34GroupEndTuple_injective A T h) i,
      fun h => congrArg (e34GroupEndTuple A T) (funext h)⟩
  constructor
  · rintro ⟨f, h, he⟩
    exact ⟨f, (hf f).mp h, fun k hk => he k ((hf k).mpr hk)⟩
  · rintro ⟨f, h, he⟩
    exact ⟨f, (hf f).mpr h, fun k hk => he k ((hf k).mp hk)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.BoundedEndomorphismTuples
