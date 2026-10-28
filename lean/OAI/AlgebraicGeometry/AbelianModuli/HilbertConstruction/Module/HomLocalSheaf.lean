import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomBaseChange
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Sheaf

/-! # Hom Local Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomLocalSheaf

noncomputable section

/-! Sheaf descent can be checked after replacing the base by a test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (T : Over X)

def sliceIdentityIso : (Over.map T.hom).obj (Over.mk (𝟙 T.left)) ≅ T :=
  Over.isoMk (Iso.refl T.left) rfl

def sliceBaseChangeSieve (S : Sieve T) : Sieve (Over.mk (𝟙 T.left)) :=
  (Sieve.overEquiv (Over.mk (𝟙 T.left))).symm (Sieve.overEquiv T S)

theorem sliceBaseChangeSieve_push_pull (S : Sieve T) :
    ((sliceBaseChangeSieve T S).functorPushforward (Over.map T.hom)).pullback (sliceIdentityIso T).inv = S := by
  apply (Sieve.overEquiv T).injective
  rw [Sieve.overEquiv_pullback, sliceBaseChangeSieve, Sieve.functorPushforward_over_map,
    OrderIso.apply_symm_apply]
  change (Sieve.overEquiv T S).pullback (𝟙 T.left) = Sieve.overEquiv T S
  exact Sieve.pullback_id

theorem moduleHom_isSheafFor_of_baseChange (J : GrothendieckTopology Scheme.{u})
    (M N : X.Modules)
    (hF : Presheaf.IsSheaf (J.over T.left)
      (HomPresheaf.moduleHomPresheaf ((Scheme.Modules.pullback T.hom).obj M) ((Scheme.Modules.pullback T.hom).obj N)))
    (S : Sieve T) (hS : S ∈ (J.over X) T) :
    Presieve.IsSheafFor (HomPresheaf.moduleHomPresheaf M N) S.arrows := by
  have hR : sliceBaseChangeSieve T S ∈ (J.over T.left) (Over.mk (𝟙 T.left)) :=
    J.overEquiv_symm_mem_over _ _ hS
  have h := (isSheaf_iff_isSheaf_of_type _ _).mp hF _ hR
  have h' := Presieve.isSheafFor_iso (HomBaseChange.moduleHomBaseChangeIso T.hom M N) h
  have h'' := (Presieve.isSheafFor_over_map_op_comp_iff T.hom (HomPresheaf.moduleHomPresheaf M N)
    (sliceBaseChangeSieve T S) (sliceIdentityIso T)).mp h'
  rw [sliceBaseChangeSieve_push_pull] at h''
  exact h''

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomLocalSheaf
