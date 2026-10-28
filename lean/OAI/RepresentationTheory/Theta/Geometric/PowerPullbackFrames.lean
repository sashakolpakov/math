import OAI.RepresentationTheory.Theta.Geometric.PowerOpenFrameRestriction
import OAI.RepresentationTheory.Theta.Geometric.Pullback.OpenFrameRestriction
import OAI.RepresentationTheory.Theta.Geometric.OpenSectionPullback

/-! # Power Pullback Frames -/

namespace OAI.RepresentationTheory.Theta.Geometric.PowerPullbackFrames

noncomputable section

/-! Frames for power-then-pullback and pullback-then-power have identical
native restriction and scalar laws along arbitrary scheme morphisms. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

def powerThenPullbackFrame {X Y : Scheme} (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (e : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) (n : ℕ) :
    ((Scheme.Modules.pullback f).obj (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule M n)).restrict (f ⁻¹ᵁ U).ι ≅
      AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (f ⁻¹ᵁ U).toScheme :=
  Pullback.Algebraic.pullbackOpenFrame f (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule M n) U (AlgebraicPowerFrames.tensorPowerOpenFrame M U e n)

def pullbackThenPowerFrame {X Y : Scheme} (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (e : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) (n : ℕ) :
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule ((Scheme.Modules.pullback f).obj M) n).restrict (f ⁻¹ᵁ U).ι ≅
      AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (f ⁻¹ᵁ U).toScheme :=
  AlgebraicPowerFrames.tensorPowerOpenFrame _ (f ⁻¹ᵁ U) (Pullback.Algebraic.pullbackOpenFrame f M U e) n

theorem powerThenPullbackFrame_restrict {X Y : Scheme} (f : X ⟶ Y) (M : Y.Modules)
    {U V : Y.Opens} (h : V ≤ U) (e : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) (n : ℕ) :
    AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (f.preimage_mono h) (powerThenPullbackFrame f M U e n) =
      powerThenPullbackFrame f M V (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h e) n := by
  unfold powerThenPullbackFrame
  rw [Pullback.OpenFrameRestriction.pullbackOpenFrame_restrict, PowerOpenFrameRestriction.tensorPowerOpenFrame_restrict]

theorem pullbackThenPowerFrame_restrict {X Y : Scheme} (f : X ⟶ Y) (M : Y.Modules)
    {U V : Y.Opens} (h : V ≤ U) (e : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) (n : ℕ) :
    AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (f.preimage_mono h) (pullbackThenPowerFrame f M U e n) =
      pullbackThenPowerFrame f M V (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h e) n := by
  unfold pullbackThenPowerFrame
  rw [PowerOpenFrameRestriction.tensorPowerOpenFrame_restrict, Pullback.OpenFrameRestriction.pullbackOpenFrame_restrict]

theorem powerThenPullbackFrame_scalar {X Y : Scheme} (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (e g : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) (r : Γ(Y, U))
    (h : e.hom = g.hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (U.topIso.inv r)) (n : ℕ) :
    (powerThenPullbackFrame f M U e n).hom =
      (powerThenPullbackFrame f M U g n).hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection
        ((f ⁻¹ᵁ U).topIso.inv (f.app U r ^ n)) := by
  have hp := AlgebraicPowerFrames.tensorPowerOpenFrame_scalar M U e g (U.topIso.inv r) h n
  have hh := Pullback.Algebraic.pullbackOpenFrame_scalar f (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule M n) U _ _ _ hp
  apply hh.trans
  congr 2
  rw [map_pow, OpenSectionPullback.morphismRestrict_topSection_apply, map_pow]

theorem pullbackThenPowerFrame_scalar {X Y : Scheme} (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (e g : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) (r : Γ(Y, U))
    (h : e.hom = g.hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (U.topIso.inv r)) (n : ℕ) :
    (pullbackThenPowerFrame f M U e n).hom =
      (pullbackThenPowerFrame f M U g n).hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection
        ((f ⁻¹ᵁ U).topIso.inv (f.app U r ^ n)) := by
  have hp := Pullback.Algebraic.pullbackOpenFrame_scalar f M U e g (U.topIso.inv r) h
  have hh := AlgebraicPowerFrames.tensorPowerOpenFrame_scalar ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U) _ _ _ hp n
  apply hh.trans
  congr 2
  rw [OpenSectionPullback.morphismRestrict_topSection_apply, map_pow]

end

end OAI.RepresentationTheory.Theta.Geometric.PowerPullbackFrames
