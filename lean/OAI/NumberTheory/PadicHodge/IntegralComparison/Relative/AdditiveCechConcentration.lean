import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Concentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.CoefficientTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleAdditiveSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.SupportedCoordinates

/-! # Additive Cech Concentration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.AdditiveCechConcentration

noncomputable section

/-! The original additive relative Čech source preserves the canonical
concentration of a quasicoherent complex on affine intersections. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration
variable {X : Scheme.{u}} [X.IsSeparated]
  (U : X.Opens) (hU : IsAffineOpen U)
  {ι : Type u} [LinearOrder ι] (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i))

abbrev presheaves : X.Modules ⥤ X.Opensᵒᵖ ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf X.ringCatSheaf ⋙
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

instance presheaves_additive : (presheaves (X := X)).Additive where
  map_add := rfl

abbrev coefficients (K : CochainComplex X.Modules ℕ) :=
  ((presheaves (X := X)).mapHomologicalComplex (.up ℕ)).obj K

abbrev coefficientMap {K L : CochainComplex X.Modules ℕ} (a : K ⟶ L) :=
  ((presheaves (X := X)).mapHomologicalComplex (.up ℕ)).map a

def totalFunctor : CochainComplex X.Modules ℕ ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
  (presheaves (X := X)).mapHomologicalComplex (.up ℕ) ⋙
    (RelativeCech.Total.localFunctor U V).mapHomologicalComplex (.up ℕ) ⋙
      HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (.up ℕ) (.up ℕ) (.up ℕ)

def functor (q : ℕ) : CochainComplex X.Modules ℕ ⥤ AddCommGrpCat.{u} :=
  AdditiveCechConcentration.totalFunctor U V ⋙ homologyFunctor AddCommGrpCat.{u} (.up ℕ) q

include hU hV in
theorem quasiIso {K L : CochainComplex X.Modules ℕ}
    [∀ q, (K.X q).IsQuasicoherent] [∀ q, (L.X q).IsQuasicoherent]
    (a : K ⟶ L) [QuasiIso a] : QuasiIso ((AdditiveCechConcentration.totalFunctor U V).map a) := by
  let := RelativeCech.CoefficientQuasiIso.quasiIso (𝟙 X) U hU V hV a
  exact RelativeCech.CoefficientTotal.quasiIso U V
    (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u})
    (RelativeCech.CoefficientQuasiIso.coefficientMap (𝟙 X) a)

variable (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)

include hU hV hK in
theorem projection_isIso (q : ℕ) : IsIso ((functor U V q).map (CohomologyConcentration.projection K c)) := by
  let (k : ℕ) := QuasicoherentTruncation.truncation K c k
  let := CohomologyConcentration.projection_quasiIso K c hK
  let := quasiIso U hU V hV (CohomologyConcentration.projection K c)
  change IsIso (homologyMap ((AdditiveCechConcentration.totalFunctor U V).map (CohomologyConcentration.projection K c)) q)
  infer_instance

include hU hV hK in
theorem inclusion_isIso (q : ℕ) : IsIso ((functor U V q).map (CohomologyConcentration.inclusion K c)) := by
  let (k : ℕ) := QuasicoherentTruncation.truncation K c k
  let := QuasicoherentTruncation.cohomology K c
  let (k : ℕ) := QuasicoherentTruncation.single (K.homology c) c k
  let := CohomologyConcentration.inclusion_quasiIso K c hK
  let := quasiIso U hU V hV (CohomologyConcentration.inclusion K c)
  change IsIso (homologyMap ((AdditiveCechConcentration.totalFunctor U V).map (CohomologyConcentration.inclusion K c)) q)
  infer_instance

def iso (q : ℕ) := by
  letI := projection_isIso U hU V hV K c hK q
  letI := inclusion_isIso U hU V hV K c hK q
  exact Functor.ConcentrationSingle.iso (functor U V q) K c

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.AdditiveCechConcentration
