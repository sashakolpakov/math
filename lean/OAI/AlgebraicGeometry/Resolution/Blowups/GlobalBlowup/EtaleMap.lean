import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.SpecifiedMap
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.FlatBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.GlobalCoefficientEtalePullback

/-! # Etale Map -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.EtaleMap.Construction

noncomputable section

/-! Étale maps induce étale comparisons between the actual global blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem affineBlowupMapTo_etale {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (φ : R →+* S) (h : I.map φ = J) (hφ : φ.Etale) :
    Etale (Blowup.Functor.Construction.affineBlowupMapTo I J φ h) := by
  subst J
  let : Algebra R S := φ.toAlgebra
  let : Algebra.Etale R S := (RingHom.etale_algebraMap (R := R) (S := S)).mp hφ
  exact Blowup.FlatBaseChange.Construction.affineBlowupMap_etale I

theorem globalBlowupMap_etale
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ X) [Etale q]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (hY : I.comap q ≠ ⊥) :
    Etale (FunctorialMap.Construction.globalBlowupMap q I hI hY) := by
  choose U V hsub hmem using IdealSheaf.ProductPullback.Construction.exists_affine_pair_at_point q
  have hcover : ⨆ y : Y, (V y).1 = ⊤ := by
    apply top_le_iff.mp
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hmem y⟩
  let : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Etale)
  apply IsZariskiLocalAtSource.of_openCover (P := @Etale)
    (MapGluing.Construction.globalBlowupChosenCover (I.comap q) hY V hcover)
  intro y
  change Y at y
  change Etale (Data.Construction.globalBlowupChart (I.comap q) hY (V y) ≫ FunctorialMap.Construction.globalBlowupMap q I hI hY)
  rw [FunctorialMap.Construction.globalBlowupMap_chart q I hI hY (U y) (V y) (hsub y)]
  let : Etale (Blowup.Functor.Construction.affineBlowupMapTo (I.ideal (U y)) ((I.comap q).ideal (V y))
      (q.appLE (U y).1 (V y).1 (hsub y)).hom
      (IdealSheaf.AffinePullback.Construction.idealSheaf_comap_ideal_of_le I q (U y) (V y) (hsub y)).symm) :=
    affineBlowupMapTo_etale _ _ _ _ (q.etale_appLE (U y).2 (V y).2 (hsub y))
  infer_instance

theorem globalBlowupMapTo_etale
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ X) [Etale q]
    (I : X.IdealSheafData) (K : Y.IdealSheafData)
    (hq : I.comap q = K) (hI : I ≠ ⊥) (hK : K ≠ ⊥) :
    Etale (SpecifiedMap.Construction.globalBlowupMapTo q I K hq hI hK) := by
  subst K
  exact globalBlowupMap_etale q I hI hK

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.EtaleMap.Construction
