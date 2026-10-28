import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Local
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ExceptionalPrincipality
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.OpenMap
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.AffinePullback

/-! # Functorial Map -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.FunctorialMap.Construction

noncomputable section

section

/-! Functorial maps between actual global blowups of integral schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  [IsIntegral Y] [IsLocallyNoetherian Y]

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- The center remains nonzero on the blowup of its pullback. -/
theorem globalBlowupMap_center_ne_bot (q : Y ⟶ X) (I : X.IdealSheafData)
    (hY : I.comap q ≠ ⊥) :
    I.comap (Data.Construction.globalBlowupToBase (I.comap q) hY ≫ q) ≠ ⊥ := by
  rw [Scheme.IdealSheafData.comap_comp]
  exact Nonzero.Construction.globalBlowup_totalIdeal_ne_bot (I.comap q) (I.comap q) hY hY

/-- The universal property constructs the comparison for any actual morphism
whose pulled-back center is nonzero. -/
def globalBlowupMap (q : Y ⟶ X) (I : X.IdealSheafData)
    (hI : I ≠ ⊥) (hY : I.comap q ≠ ⊥) :
    Data.Construction.globalBlowup (I.comap q) hY ⟶ Data.Construction.globalBlowup I hI :=
  Local.Construction.globalBlowupUniversalLift I hI (Data.Construction.globalBlowupToBase (I.comap q) hY ≫ q)
    (globalBlowupMap_center_ne_bot q I hY) (by
      rw [Scheme.IdealSheafData.comap_comp]
      exact Global.ExceptionalPrincipality.Construction.globalBlowup_center_locallyPrincipal (I.comap q) hY)

theorem globalBlowupMap_over (q : Y ⟶ X) (I : X.IdealSheafData)
    (hI : I ≠ ⊥) (hY : I.comap q ≠ ⊥) :
    globalBlowupMap q I hI hY ≫ Data.Construction.globalBlowupToBase I hI =
      Data.Construction.globalBlowupToBase (I.comap q) hY ≫ q :=
  Local.Construction.globalBlowupUniversalLift_over I hI _ _ _

/-- The comparison is the unique morphism over the original base map. -/
theorem globalBlowupMap_unique (q : Y ⟶ X) (I : X.IdealSheafData)
    (hI : I ≠ ⊥) (hY : I.comap q ≠ ⊥)
    (g : Data.Construction.globalBlowup (I.comap q) hY ⟶ Data.Construction.globalBlowup I hI)
    (hg : g ≫ Data.Construction.globalBlowupToBase I hI = Data.Construction.globalBlowupToBase (I.comap q) hY ≫ q) :
    g = globalBlowupMap q I hI hY :=
  Local.Construction.globalBlowup_hom_ext I hI _ (globalBlowupMap_center_ne_bot q I hY)
    g _ hg (globalBlowupMap_over q I hI hY)

/-- The universal comparison agrees with the previously constructed open map. -/
theorem globalBlowupMap_eq_openMap (q : Y ⟶ X) [IsOpenImmersion q]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hY : I.comap q ≠ ⊥) :
    globalBlowupMap q I hI hY = OpenMap.Construction.globalBlowupOpenMap q I hI hY :=
  (globalBlowupMap_unique q I hI hY _ (OpenMap.Construction.globalBlowupOpenMap_over q I hI hY)).symm

end

/-! The universal global blowup comparison agrees with actual affine Rees maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  [IsIntegral Y] [IsLocallyNoetherian Y]

theorem globalBlowupMap_chart (q : Y ⟶ X) (I : X.IdealSheafData)
    (hI : I ≠ ⊥) (hY : I.comap q ≠ ⊥)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ q ⁻¹ᵁ U.1) :
    Data.Construction.globalBlowupChart (I.comap q) hY V ≫ globalBlowupMap q I hI hY =
      Blowup.Functor.Construction.affineBlowupMapTo (I.ideal U) ((I.comap q).ideal V) (q.appLE U.1 V.1 hVU).hom
        (IdealSheaf.AffinePullback.Construction.idealSheaf_comap_ideal_of_le I q U V hVU).symm ≫ Data.Construction.globalBlowupChart I hI U := by
  let j := Data.Construction.globalBlowupChart (I.comap q) hY V
  let π := Data.Construction.globalBlowupToBase (I.comap q) hY
  let : IsReduced (ReesGrading.Construction.affineBlowup ((I.comap q).ideal V)) := isReduced_of_isOpenImmersion j
  have hd : Dense (((π ≫ q) ⁻¹ᵁ I.support.compl : (Data.Construction.globalBlowup (I.comap q) hY).Opens) :
      Set (Data.Construction.globalBlowup (I.comap q) hY)) := by
    have h := Local.Construction.idealSheaf_supportComplement_dense (I.comap (π ≫ q))
      (globalBlowupMap_center_ne_bot q I hY)
    rw [Scheme.IdealSheafData.support_comap] at h
    exact h
  apply Local.Construction.globalBlowup_hom_ext_of_dense_complement I hI (j ≫ (π ≫ q))
    (hd.preimage j.isOpenEmbedding.isOpenMap)
  · rw [Category.assoc, globalBlowupMap_over]
  · rw [Category.assoc, Data.Construction.globalBlowupChart_over, ← Category.assoc,
      Blowup.Functor.Construction.affineBlowupMapTo_over, Category.assoc]
    change ReesGrading.Construction.affineBlowupToSpec ((I.comap q).ideal V) ≫
      (Spec.map (q.appLE U.1 V.1 hVU) ≫ U.2.fromSpec) = _
    rw [IsAffineOpen.SpecMap_appLE_fromSpec q U.2 V.2 hVU]
    change _ = Data.Construction.globalBlowupChart (I.comap q) hY V ≫
      (Data.Construction.globalBlowupToBase (I.comap q) hY ≫ q)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ q) (Data.Construction.globalBlowupChart_over (I.comap q) hY V).symm).trans
        (Category.assoc _ _ _))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.FunctorialMap.Construction
