import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Closed
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.SectionPullback

/-! # Cech Cover Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.CechCoverTransport.Construction

noncomputable section

/-! Literal transport between equal original covers preserves their
Cech cochains and native H1 classes. Pair-intersection coordinates are
identified by the actual section transport, rather than an assumed
cochain compatibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Scheme.{0}) {I : Type} {U V : I → X.Opens}

def regularCechCoverTransport (h : U = V) {n : ℕ}
    (c : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (AbelianModuli.ReferenceFamily.Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U n) :
    DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (AbelianModuli.ReferenceFamily.Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj V n := by
  subst V
  exact c

theorem regularCechCoverTransport_apply (h : U = V) {n : ℕ}
    (c : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (AbelianModuli.ReferenceFamily.Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U n) (a : Fin (n + 1) → I) :
    regularCechCoverTransport X h c a =
      AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (congrArg (fun W => AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection W a) h) (c a) := by
  subst V
  rfl

theorem regularCechCoverTransport_closed (h : U = V) {n : ℕ}
    (c : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (AbelianModuli.ReferenceFamily.Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U n)
    (hc : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (AbelianModuli.ReferenceFamily.Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U n c = 0) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (AbelianModuli.ReferenceFamily.Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj V n (regularCechCoverTransport X h c) = 0 := by
  subst V
  exact hc

theorem regularCechCoverTransport_sheafClass (h : U = V) (hU : iSup U = ⊤) (hV : iSup V = ⊤)
    (c : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (AbelianModuli.ReferenceFamily.Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 1)
    (hc : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (AbelianModuli.ReferenceFamily.Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 1 c = 0) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass V (AbelianModuli.ReferenceFamily.Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hV 0
      (regularCechCoverTransport X h c) (regularCechCoverTransport_closed X h c hc) =
      DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U (AbelianModuli.ReferenceFamily.Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hU 0 c hc := by
  subst V
  rfl

theorem regularPairCechCochain_coverTransport (h : U = V)
    (v : ∀ i j, Γ(X, U i ⊓ U j)) :
    regularCechCoverTransport X h (AbelianModuli.ReferenceFamily.RegularPair.Closed.regularPairCechCochain X U v) =
      AbelianModuli.ReferenceFamily.RegularPair.Closed.regularPairCechCochain X V (fun i j =>
        AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (congrArg (fun W => W i ⊓ W j) h) (v i j)) := by
  subst V
  rfl

theorem originalPairCechIntersection (U : I → X.Opens) (a : Fin 2 → I) :
    AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a = U (a 0) ⊓ U (a 1) := by
  ext x
  constructor
  · intro hx
    have h := (AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection U a x).mp hx
    exact ⟨h 0, h 1⟩
  · intro hx
    apply (AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection U a x).mpr
    exact Fin.cases hx.1 (Fin.cases hx.2 (fun i => Fin.elim0 i))

theorem originalPairCechCochain_transport (U : I → X.Opens)
    (v : ∀ i j, Γ(X, U i ⊓ U j)) (a : Fin 2 → I) :
    AbelianModuli.ReferenceFamily.RegularPair.Closed.regularPairCechCochain X U v a =
      AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport (originalPairCechIntersection X U a).symm (v (a 0) (a 1)) := by
  rw [AbelianModuli.ReferenceFamily.RegularPair.Closed.regularPairCechCochain, AbelianModuli.ReferenceFamily.FixedFiber.SectionPullback.regularSectionTransport_eq_map]
  exact congrArg (fun f => X.presheaf.map f (v (a 0) (a 1))) (Subsingleton.elim _ _)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.CechCoverTransport.Construction
