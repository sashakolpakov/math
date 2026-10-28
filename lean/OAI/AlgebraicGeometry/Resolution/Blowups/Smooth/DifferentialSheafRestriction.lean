import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialIdealSheaf
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.ComplexNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialEquiv
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Differential Sheaf Restriction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialSheafRestriction.Construction

noncomputable section

/-! The intrinsic differential ideal sheaf commutes with arbitrary open-chart pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme} (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]

/-- The differential ideal sheaf respects every actual open immersion,
using the complex structures induced by the original structure map. -/
theorem smoothDifferentialIdealSheaf_comap_open (I : Y.IdealSheafData) (n : ℕ)
    (g : X ⟶ Y) [IsOpenImmersion g] :
    (DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f I n).comap g =
      DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (g ≫ f) (I.comap g) n := by
  apply Scheme.IdealSheafData.ext
  funext U
  let V : Y.affineOpens := ⟨g ''ᵁ U.1, U.2.image_of_isOpenImmersion g⟩
  let : Algebra ℂ Γ(Y, V) := DifferentialIdealSheaf.Construction.affineComplexAlgebra f V
  let : Algebra ℂ Γ(X, U) := DifferentialIdealSheaf.Construction.affineComplexAlgebra (g ≫ f) U
  let e : Γ(Y, V) ≃ₐ[ℂ] Γ(X, U) :=
    { __ := (g.appIso U.1).commRingCatIsoToRingEquiv
      commutes' c := RingHom.congr_fun (Affine.ComplexNaturality.Construction.affineComplexScalars_appIso f g U) c }
  let : Algebra.Smooth ℂ Γ(Y, V) := DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f V
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  change (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ (I.ideal V) n).comap e.symm.toRingHom =
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ ((I.comap g).ideal U) n
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact DifferentialEquiv.Construction.smooth_relativeDifferentialIdeal_comap_equiv ℂ e (I.ideal V) n

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialSheafRestriction.Construction
