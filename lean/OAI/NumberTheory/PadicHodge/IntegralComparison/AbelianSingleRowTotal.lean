import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.RowTotalNaturality

/-! # Abelian Single Row Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AbelianSingleRowTotal

noncomputable section

/-! The original total of an abelian-category bicomplex supported in
one row, with its actual shift and naturality under bicomplex maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentrationNaturality

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]
  (B : HomologicalComplex₂ C (.up ℕ) (.up ℕ))

def projection (p q n : ℕ) (_h : p + q = n) :
    (B.total (.up ℕ)).X n ⟶ (B.X p).X q :=
  B.totalDesc (fun a b _ =>
    if ha : a = p then
      if hb : b = q then (B.XXIsoOfEq _ _ _ ha hb).hom else 0
    else 0)

variable (c : ℕ) (hB : ∀ p q, q ≠ c → IsZero ((B.X p).X q))

def componentIso (p : ℕ) : (B.X p).X c ≅ (B.total (.up ℕ)).X (p + c) where
  hom := B.ιTotal (.up ℕ) p c (p + c) rfl
  inv := projection B p c (p + c) rfl
  hom_inv_id := by simp [projection]
  inv_hom_id := by
    apply HomologicalComplex₂.total.hom_ext
    intro a b hab
    by_cases hb : b = c
    · subst b
      have ha : a = p := by change a + c = p + c at hab; omega
      subst a
      simp [projection]
    · exact (hB a b hb).eq_of_src _ _

def restrictionIso : B.flip.X c ≅ (B.total (.up ℕ)).restriction (CohomologyConcentration.shift c) :=
  HomologicalComplex.Hom.isoOfComponents (componentIso B c hB) (by
    intro p p' hp
    have hp' : p + 1 = p' := hp
    subst p'
    change B.ιTotal (.up ℕ) p c (p + c) rfl ≫
      (B.total (.up ℕ)).d (p + c) (p + 1 + c) =
        (B.d p (p + 1)).f c ≫ B.ιTotal (.up ℕ) (p + 1) c (p + 1 + c) rfl
    have hz : (B.X p).d c (c + 1) = 0 := (hB p (c + 1) (by omega)).eq_of_tgt _ _
    rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
      B.d₁_eq (.up ℕ) (show (ComplexShape.up ℕ).Rel p (p + 1) from rfl) c (p + 1 + c) rfl,
      B.d₂_eq (.up ℕ) p (show (ComplexShape.up ℕ).Rel c (c + 1) from rfl)
        (p + 1 + c) (by change p + (c + 1) = p + 1 + c; omega),
      hz, zero_comp, smul_zero, add_zero]
    simp only [AlgebraicTopology.DeRham.Comparison.DoubleComplexSigns.DoubleComplex.epsilon1_upNat, one_smul])

include hB in
theorem supported : (B.total (.up ℕ)).IsStrictlySupported (CohomologyConcentration.shift c) := by
  constructor
  intro n hn
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  change p + q = n at hpq
  have hq : q ≠ c := by
    intro hq
    apply hn p
    change p + c = n
    simpa only [hq] using hpq
  exact (hB p q hq).eq_of_src _ _

def homologyIso (n : ℕ) :
    (B.total (.up ℕ)).homology (n + c) ≅ (B.flip.X c).homology n := by
  let : (B.total (.up ℕ)).IsStrictlySupported (CohomologyConcentration.shift c) := supported B c hB
  exact Single.RowTotalNaturality.supportedIso (B.total (.up ℕ)) c n ≪≫
    (HomologicalComplex.homologyMapIso (restrictionIso B c hB) n).symm

variable {B} {D : HomologicalComplex₂ C (.up ℕ) (.up ℕ)} (a : B ⟶ D)
  (hD : ∀ p q, q ≠ c → IsZero ((D.X p).X q))

def rowMap : B.flip.X c ⟶ D.flip.X c :=
  ((HomologicalComplex₂.flipFunctor C (.up ℕ) (.up ℕ)).map a).f c

theorem restriction_naturality :
    rowMap c a ≫ (restrictionIso D c hD).hom =
      (restrictionIso B c hB).hom ≫
        HomologicalComplex.restrictionMap (HomologicalComplex₂.total.map a (.up ℕ)) (CohomologyConcentration.shift c) := by
  apply HomologicalComplex.Hom.ext
  funext p
  change (a.f p).f c ≫ D.ιTotal (.up ℕ) p c (p + c) rfl =
    B.ιTotal (.up ℕ) p c (p + c) rfl ≫ (HomologicalComplex₂.total.map a (.up ℕ)).f (p + c)
  exact (HomologicalComplex₂.ιTotal_map B D a (.up ℕ) p c (p + c) rfl).symm

theorem homology_naturality (n : ℕ) :
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map a (.up ℕ)) (n + c) ≫
        (homologyIso D c hD n).hom =
      (homologyIso B c hB n).hom ≫ HomologicalComplex.homologyMap (rowMap c a) n := by
  let : (B.total (.up ℕ)).IsStrictlySupported (CohomologyConcentration.shift c) := supported B c hB
  let : (D.total (.up ℕ)).IsStrictlySupported (CohomologyConcentration.shift c) := supported D c hD
  have hs := Single.RowTotalNaturality.supported_naturality c
    (HomologicalComplex₂.total.map a (.up ℕ)) n
  have hr := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (restriction_naturality c hB a hD)
  simp only [HomologicalComplex.homologyMap_comp] at hr
  have hi := CohomologyConcentrationNaturality.inverse_square _ _
    (HomologicalComplex.homologyMapIso (restrictionIso B c hB) n)
    (HomologicalComplex.homologyMapIso (restrictionIso D c hD) n) hr
  simpa only [homologyIso, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex.homologyMapIso_hom, Category.assoc] using
      DualComplexHomology.compose_squares _ _ _ _ _ _ _ hs hi

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AbelianSingleRowTotal
