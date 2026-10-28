import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.RowTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentrationNaturality

/-! # Row Total Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Single.RowTotalNaturality

noncomputable section

/-! Naturality of the actual cohomology shift for a total complex
supported in a single row. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

universe u v

open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentrationNaturality

section Supported

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : CochainComplex C ℕ) (c : ℕ) [K.IsStrictlySupported (CohomologyConcentration.shift c)]

def supportedIso (n : ℕ) : K.homology (n + c) ≅ (K.restriction (CohomologyConcentration.shift c)).homology n := by
  let e := CohomologyConcentration.shift c
  have : IsIso (K.restrictionToTruncGE' e) := HomologicalComplex.Hom.isIso_of_components _
  exact HomologicalComplex.homologyMapIso (asIso (K.πTruncGE e)) (n + c) ≪≫
    (K.truncGE' e).extendHomologyIso e rfl ≪≫
    (HomologicalComplex.homologyMapIso (asIso (K.restrictionToTruncGE' e)) n).symm

variable {K} {L : CochainComplex C ℕ} [L.IsStrictlySupported (CohomologyConcentration.shift c)] (a : K ⟶ L)

@[reassoc]
theorem supported_naturality (n : ℕ) :
    HomologicalComplex.homologyMap a (n + c) ≫ (supportedIso L c n).hom =
      (supportedIso K c n).hom ≫ HomologicalComplex.homologyMap
        (HomologicalComplex.restrictionMap a (CohomologyConcentration.shift c)) n := by
  let e := CohomologyConcentration.shift c
  have : IsIso (K.restrictionToTruncGE' e) := HomologicalComplex.Hom.isIso_of_components _
  have : IsIso (L.restrictionToTruncGE' e) := HomologicalComplex.Hom.isIso_of_components _
  have hπ := congrArg (fun f => HomologicalComplex.homologyMap f (n + c))
    (HomologicalComplex.πTruncGE_naturality a e).symm
  simp only [HomologicalComplex.homologyMap_comp] at hπ
  have he := HomologicalComplex.extendHomologyIso_hom_naturality
    (HomologicalComplex.truncGE'Map a e) e (show e.f n = n + c from rfl)
  have hr := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (HomologicalComplex.restrictionToTruncGE'_naturality a e).symm
  simp only [HomologicalComplex.homologyMap_comp] at hr
  have hi := CohomologyConcentrationNaturality.inverse_square _ _
    (HomologicalComplex.homologyMapIso (asIso (K.restrictionToTruncGE' e)) n)
    (HomologicalComplex.homologyMapIso (asIso (L.restrictionToTruncGE' e)) n) hr
  have hehi := DualComplexHomology.compose_squares _ _ _ _ _ _ _ he hi
  simpa only [supportedIso, Iso.trans_hom, Iso.symm_hom, HomologicalComplex.homologyMapIso_hom,
    asIso_hom, Category.assoc, e] using
    DualComplexHomology.compose_squares _ _ _ _ _ _ _ hπ hehi

end Supported

variable {R : Type u} [CommRing R]
  {B D : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ)}
  (a : B ⟶ D) (c : ℕ)
  (hB : ∀ p q, q ≠ c → IsZero ((B.X p).X q))
  (hD : ∀ p q, q ≠ c → IsZero ((D.X p).X q))

def rowMap : B.flip.X c ⟶ D.flip.X c :=
  ((HomologicalComplex₂.flipFunctor (ModuleCat.{v} R) (.up ℕ) (.up ℕ)).map a).f c

@[reassoc]
theorem restriction_naturality :
    rowMap a c ≫ (RowTotal.restrictionIso D c hD).hom =
      (RowTotal.restrictionIso B c hB).hom ≫
        HomologicalComplex.restrictionMap (HomologicalComplex₂.total.map a (.up ℕ)) (CohomologyConcentration.shift c) := by
  apply HomologicalComplex.Hom.ext
  funext p
  change (a.f p).f c ≫ D.ιTotal (.up ℕ) p c (p + c) rfl =
    B.ιTotal (.up ℕ) p c (p + c) rfl ≫ (HomologicalComplex₂.total.map a (.up ℕ)).f (p + c)
  exact (HomologicalComplex₂.ιTotal_map B D a (.up ℕ) p c (p + c) rfl).symm

@[reassoc]
theorem homology_naturality (n : ℕ) :
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map a (.up ℕ)) (n + c) ≫
        (RowTotal.homologyIso D c hD n).hom =
      (RowTotal.homologyIso B c hB n).hom ≫
        HomologicalComplex.homologyMap (rowMap a c) n := by
  let : (B.total (.up ℕ)).IsStrictlySupported (CohomologyConcentration.shift c) := RowTotal.supported B c hB
  let : (D.total (.up ℕ)).IsStrictlySupported (CohomologyConcentration.shift c) := RowTotal.supported D c hD
  have hs := supported_naturality c (HomologicalComplex₂.total.map a (.up ℕ)) n
  have hr := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (restriction_naturality a c hB hD)
  simp only [HomologicalComplex.homologyMap_comp] at hr
  have hi := CohomologyConcentrationNaturality.inverse_square _ _
    (HomologicalComplex.homologyMapIso (RowTotal.restrictionIso B c hB) n)
    (HomologicalComplex.homologyMapIso (RowTotal.restrictionIso D c hD) n) hr
  simpa only [RowTotal.homologyIso, supportedIso, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex.homologyMapIso_hom, Category.assoc] using
    DualComplexHomology.compose_squares _ _ _ _ _ _ _ hs hi

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Single.RowTotalNaturality
