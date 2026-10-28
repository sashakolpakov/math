import OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Transport

/-! # Coefficient Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CoefficientCoordinates

noncomputable section

/-! Changing the named coefficient module of one fixed resolution
preserves its cohomology map when the original coefficient maps agree. -/
open _root_.CategoryTheory
set_option backward.isDefEq.respectTransparency false
universe u v w z
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] [Abelian D]
  (F : Cᵒᵖ ⥤ D) [F.Additive]
  {M S T N : C} (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
  (e : M ≅ S) (e' : M ≅ T) (f : S ⟶ N) (f' : T ⟶ N)
  (h : e.hom ≫ f = e'.hom ≫ f')

include h in
theorem map (n : ℕ) :
    CohomologyMaps.map F (IntegralComparison.ProjectiveResolution.Transport.alongIso P e) Q f n =
      CohomologyMaps.map F (IntegralComparison.ProjectiveResolution.Transport.alongIso P e') Q f' n := by
  let a := ProjectiveResolution.lift f' (IntegralComparison.ProjectiveResolution.Transport.alongIso P e') Q
  have ha : a ≫ Q.π =
      (IntegralComparison.ProjectiveResolution.Transport.alongIso P e).π ≫ (ChainComplex.single₀ C).map f := by
    have hf := ProjectiveResolution.lift_commutes f'
      (IntegralComparison.ProjectiveResolution.Transport.alongIso P e') Q
    change a ≫ Q.π = (P.π ≫ (ChainComplex.single₀ C).map e'.hom) ≫
      (ChainComplex.single₀ C).map f' at hf
    change a ≫ Q.π = (P.π ≫ (ChainComplex.single₀ C).map e.hom) ≫
      (ChainComplex.single₀ C).map f
    simpa only [Category.assoc, ← Functor.map_comp, h] using hf
  exact CohomologyMaps.map_eq F
    (IntegralComparison.ProjectiveResolution.Transport.alongIso P e) Q f a ha n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CoefficientCoordinates
