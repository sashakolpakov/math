import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Power
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Group

/-! # Frobenius Level -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FrobeniusLevel.Construction

noncomputable section

/-!
Relative Frobenius transports the full marking to the Frobenius twist.
This follows from scheme Frobenius naturality and the fact that absolute
Frobenius is the identity on the underlying topological space, on which
the constant-level functor is evaluated.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S S' : Scheme.{u}} {g N : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}

theorem pulledBackLevel_projection
    (level : A.FullLevel N) (f : S' ⟶ S) (T : Over S')
    (c : (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S').obj (op T)) :
    ((level.pullback f).hom.app (op T) c).val.left ≫ pullback.fst A.scheme.hom f =
      (level.hom.app (op ((Over.map f).obj T)) c).val.left := by
  exact congrArg (fun x => x.val.left)
    ((A.torsionBaseChangeEquiv f T N).apply_symm_apply
      (level.hom.app (op ((Over.map f).obj T)) c))

/-- The full marking, including the chosen basis, is transported by
relative Frobenius exactly to the marking on the base-changed object. -/
theorem relativeFrobenius_transports_level
    (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0)
    (level : A.FullLevel N) (T : Over S)
    (c : (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S).obj (op T)) :
    ((level.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp S hS)).hom.app (op T) c).val =
      (level.hom.app (op T) c).val ≫ Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS A.scheme := by
  let fS := Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp S hS
  let hT := Picard.Homomorphisms.Frobenius.Construction.prime_eq_zero_of_map p hS T.hom
  let fT := Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp T.left hT
  let t : (Over.map fS).obj T ⟶ T :=
    Over.homMk fT (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius_naturality p hp hT hS T.hom)
  have hc : (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S).map t.op c = c := by
    change LocallyConstant.comap ⟨fT, fT.continuous⟩ c = c
    exact LocallyConstant.ext (fun _ => rfl)
  have hnat := congrArg
    (fun k : (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S).obj (op T) ⟶
      (A.torsionFunctor N).obj (op ((Over.map fS).obj T)) => k.hom c)
    (level.hom.naturality t.op)
  change level.hom.app (op ((Over.map fS).obj T))
      ((AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S).map t.op c) =
    (A.torsionFunctor N).map t.op (level.hom.app (op T) c) at hnat
  rw [hc] at hnat
  have hpoint := congrArg (fun x => x.val.left) hnat
  change (level.hom.app (op ((Over.map fS).obj T)) c).val.left =
    fT ≫ (level.hom.app (op T) c).val.left at hpoint
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hright :
        ((level.hom.app (op T) c).val ≫
          Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS A.scheme).left ≫
            pullback.fst A.scheme.hom fS =
          fT ≫ (level.hom.app (op T) c).val.left := by
      change ((level.hom.app (op T) c).val.left ≫
        (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS A.scheme).left) ≫
          pullback.fst A.scheme.hom fS = _
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun z => (level.hom.app (op T) c).val.left ≫ z)
          (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius_comp_fst p hp hS A.scheme)).trans
          (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius_naturality p hp hT
            (Picard.Homomorphisms.Frobenius.Construction.prime_eq_zero_of_map p hS A.scheme.hom)
            (level.hom.app (op T) c).val.left).symm)
    exact (pulledBackLevel_projection level fS T c).trans (hpoint.trans hright.symm)
  · exact (((level.pullback fS).hom.app (op T) c).val.w).trans
      ((level.hom.app (op T) c).val ≫
        Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p hp hS A.scheme).w.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FrobeniusLevel.Construction
