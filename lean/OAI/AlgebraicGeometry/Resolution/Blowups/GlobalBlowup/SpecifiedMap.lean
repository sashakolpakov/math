import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.ClosedImmersion
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.MapControlledIdeal

/-! # Specified Map -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.SpecifiedMap.Construction

noncomputable section

/-! Global comparison maps with the pulled-back center named independently. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  [IsIntegral Y] [IsLocallyNoetherian Y]

def globalBlowupMapTo (q : Y ⟶ X) (I : X.IdealSheafData) (K : Y.IdealSheafData)
    (hq : I.comap q = K) (hI : I ≠ ⊥) (hK : K ≠ ⊥) :
    Data.Construction.globalBlowup K hK ⟶ Data.Construction.globalBlowup I hI := by
  subst K
  exact FunctorialMap.Construction.globalBlowupMap q I hI hK

theorem globalBlowupMapTo_over (q : Y ⟶ X) (I : X.IdealSheafData) (K : Y.IdealSheafData)
    (hq : I.comap q = K) (hI : I ≠ ⊥) (hK : K ≠ ⊥) :
    globalBlowupMapTo q I K hq hI hK ≫ Data.Construction.globalBlowupToBase I hI = Data.Construction.globalBlowupToBase K hK ≫ q := by
  subst K
  exact FunctorialMap.Construction.globalBlowupMap_over q I hI hK

theorem globalBlowupMapTo_isClosedImmersion (q : Y ⟶ X) [IsClosedImmersion q]
    (I : X.IdealSheafData) (K : Y.IdealSheafData)
    (hq : I.comap q = K) (hI : I ≠ ⊥) (hK : K ≠ ⊥) :
    IsClosedImmersion (globalBlowupMapTo q I K hq hI hK) := by
  subst K
  exact ClosedImmersion.Construction.globalBlowupMap_isClosedImmersion q I hI hK

theorem globalBlowupMapTo_controlledIdeal (q : Y ⟶ X) (I J : X.IdealSheafData)
    (K : Y.IdealSheafData) (hq : I.comap q = K) (hI : I ≠ ⊥) (hK : K ≠ ⊥)
    (b : ℕ) (hp : J ≤ I ^ b) :
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b).comap (globalBlowupMapTo q I K hq hI hK) =
      GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal K (J.comap q) hK b := by
  subst K
  exact MapControlledIdeal.Construction.globalBlowupMap_controlledIdeal q I J hI hK b hp

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.SpecifiedMap.Construction
