import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting
import OAI.AlgebraicGeometry.Picard.PoincareBundle.EffectiveOverQuotient

/-! # Preimage Quotient -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.PreimageQuotient

noncomputable section

/-! Restricting an actual quotient to the inverse image of a kernel is again that quotient's base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

attribute [local instance] Kernel.Scheme.kernelGroup

variable {S : Scheme.{u}} {A B D : Over S} [GrpObj A] [GrpObj B] [GrpObj D]
  (f : A ⟶ B) (m : B ⟶ D) [IsMonHom f] [IsMonHom m]

/-- The quotient restricts to the genuine scheme-theoretic inverse image of the target kernel. -/
def map : Kernel.Scheme.kernelObject (f ≫ m) ⟶ Kernel.Scheme.kernelObject m :=
  (Kernel.Scheme.kernelPointsEquiv m _).symm ⟨Kernel.Scheme.kernelInclusion (f ≫ m) ≫ f, by
    change (Kernel.Scheme.kernelInclusion (f ≫ m) ≫ f) ≫ m = 1
    rw [Category.assoc, Kernel.Scheme.kernelInclusion_comp]⟩

/-- The restricted map retains the original included scheme point. -/
theorem map_inclusion : map f m ≫ Kernel.Scheme.kernelInclusion m = Kernel.Scheme.kernelInclusion (f ≫ m) ≫ f :=
  pullback.lift_fst _ _ _

instance map_isMonHom : IsMonHom (map f m) := by
  have : IsMonHom (map f m ≫ Kernel.Scheme.kernelInclusion m) := by rw [map_inclusion]; infer_instance
  exact Splitting.isMonHom_of_mono_postcomp _ (Kernel.Scheme.kernelInclusion m)

/-- Its defining square is an actual pullback in the category of schemes over the base. -/
theorem isPullback : IsPullback (Kernel.Scheme.kernelInclusion (f ≫ m)) (map f m) f (Kernel.Scheme.kernelInclusion m) := by
  have ht : map f m ≫ pullback.snd m η[D] = pullback.snd (f ≫ m) η[D] := Subsingleton.elim _ _
  have ho : IsPullback (Kernel.Scheme.kernelInclusion (f ≫ m)) (map f m ≫ pullback.snd m η[D]) (f ≫ m) η[D] := by
    rw [ht]
    exact IsPullback.of_hasPullback (f ≫ m) η[D]
  exact ho.of_bot (map_inclusion f m).symm (IsPullback.of_hasPullback m η[D])

/-- Forgetting to schemes preserves the quotient's kernel pullback square. -/
theorem underlying_isPullback :
    IsPullback (Kernel.Scheme.kernelInclusion (f ≫ m)).left (map f m).left f.left (Kernel.Scheme.kernelInclusion m).left :=
  (Over.forget S).map_isPullback (isPullback f m)

/-- Finite flat surjectivity of the quotient is retained on the full inverse-image kernel. -/
theorem finite_flat_surjective [IsFinite f.left] [Flat f.left] [Surjective f.left] :
    IsFinite (map f m).left ∧ Flat (map f m).left ∧ Surjective (map f m).left :=
  ⟨MorphismProperty.of_isPullback (P := @IsFinite) (underlying_isPullback f m) inferInstance,
    MorphismProperty.of_isPullback (P := @Flat) (underlying_isPullback f m) inferInstance,
    MorphismProperty.of_isPullback (P := @Surjective) (underlying_isPullback f m) inferInstance⟩

/-- The restricted kernel morphism is an effective epimorphism, including for nonreduced kernels. -/
theorem effectiveEpi [IsFinite f.left] [Flat f.left] [Surjective f.left] : EffectiveEpi (map f m) := by
  obtain ⟨hf, hflat, hs⟩ := finite_flat_surjective f m
  exact EffectiveOverQuotient.affine_effective (map f m)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.PreimageQuotient
