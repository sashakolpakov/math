import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ExtensionCoordinates

/-! # Pair Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.PairCoordinates

noncomputable section

/-! Singleton and pair indices identify the original degree-zero and
degree-one Cech coordinates with their actual cover opens. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X : Scheme.{0}} {I : Type} (U : I → X.Opens)

def cechSingletonIndex (i : I) : Fin 1 → I := fun _ => i

def cechPairIndex (i j : I) : Fin 2 → I := Fin.cases i (fun _ => j)

theorem cechPairIndex_face_zero (i j : I) :
    ExtensionCoordinates.cechFaceIndex 0 0 (cechPairIndex i j) = cechSingletonIndex j := by
  funext k
  have hk : k = 0 := by omega
  subst k
  rfl

theorem cechPairIndex_face_one (i j : I) :
    ExtensionCoordinates.cechFaceIndex 0 1 (cechPairIndex i j) = cechSingletonIndex i := by
  funext k
  have hk : k = 0 := by omega
  subst k
  rfl

theorem cechIntersection_singleton (i : I) : ExtensionCoordinates.cechIntersection U 0 (cechSingletonIndex i) = U i := by
  apply le_antisymm
  · exact leOfHom (Pi.π (fun k : Fin 1 => U (cechSingletonIndex i k)) 0)
  · exact leOfHom (Pi.lift (fun _ : Fin 1 => homOfLE le_rfl))

theorem cechIntersection_pair (i j : I) :
    ExtensionCoordinates.cechIntersection U 1 (cechPairIndex i j) = U i ⊓ U j := by
  apply le_antisymm
  · exact le_inf (leOfHom (Pi.π (fun k : Fin 2 => U (cechPairIndex i j k)) 0))
      (leOfHom (Pi.π (fun k : Fin 2 => U (cechPairIndex i j k)) 1))
  · apply leOfHom (Pi.lift (fun k : Fin 2 => homOfLE ?_))
    refine Fin.cases inf_le_left (fun _ => inf_le_right) k

theorem cechCoefficient_differential_zero (W : X.Opens) (a : Γ(TermModules.cechTermModule X U 0, W))
    (i : Fin 2 → I) :
    ExtensionCoordinates.cechCoefficient U 1 W ((ModuleDifferential.cechModuleDifferential X U 0).app W a) i =
      X.presheaf.map (homOfLE (inf_le_inf_left W (ExtensionCoordinates.cechIntersection_le_face U 0 0 i))).op
        (ExtensionCoordinates.cechCoefficient U 0 W a (ExtensionCoordinates.cechFaceIndex 0 0 i)) -
      X.presheaf.map (homOfLE (inf_le_inf_left W (ExtensionCoordinates.cechIntersection_le_face U 0 1 i))).op
        (ExtensionCoordinates.cechCoefficient U 0 W a (ExtensionCoordinates.cechFaceIndex 0 1 i)) := by
  have h := ExtensionCoordinates.cechCoefficient_differential U 0 W a i
  change ExtensionCoordinates.cechCoefficient U 1 W ((ModuleDifferential.cechModuleDifferential X U 0).app W a) i =
    ∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) •
      X.presheaf.map (homOfLE (inf_le_inf_left W (ExtensionCoordinates.cechIntersection_le_face U 0 k i))).op
        (ExtensionCoordinates.cechCoefficient U 0 W a (ExtensionCoordinates.cechFaceIndex 0 k i)) at h
  simpa only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_zsmul, neg_one_zsmul, sub_eq_add_neg] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.PairCoordinates
