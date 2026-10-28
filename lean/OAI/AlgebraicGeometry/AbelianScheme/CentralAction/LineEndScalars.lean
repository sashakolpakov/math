import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Quasicoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Gluing

/-! # Line End Scalars -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LineEndScalars

noncomputable section

/-! Local frames give intrinsic scalar coordinates for endomorphisms of
actual line bundles. The coordinates will glue to a global regular function. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u
variable {X : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)

/-- A line-bundle frame on a slice site evaluates to the usual linear
isomorphism on every smaller open. -/
def lineFrameAt {U : X.Opens}
    (e : L.sheaf.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    {V : X.Opens} (h : V ≤ U) :
    L.sheaf.val.obj (.op V) ≅ ModuleCat.of Γ(X, V) Γ(X, V) :=
  (SheafOfModules.evaluation (X.ringCatSheaf.over U)
    (.op (Over.mk (homOfLE h)))).mapIso e

/-- The scalar of a line-bundle endomorphism in a frame on an open. -/
def lineEndFrameScalar (a : L.sheaf ⟶ L.sheaf) {U : X.Opens}
    (e : L.sheaf.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) : Γ(X, U) :=
  (lineFrameAt L e le_rfl).hom (a.app U ((lineFrameAt L e le_rfl).inv 1))

theorem linearFrame_scalar {R : Type u} [CommRing R] {M : ModuleCat R}
    (E : M ≅ ModuleCat.of R R) (a : M ⟶ M) (z : M) :
    a z = E.hom (a (E.inv 1)) • z := by
  let c : R := E.hom z
  have hz : z = E.inv c := (ConcreteCategory.congr_hom E.hom_inv_id z).symm
  have hc : E.inv c = c • E.inv (1 : R) := by
    simpa only [smul_eq_mul, mul_one] using E.inv.hom.map_smul c 1
  apply (ConcreteCategory.bijective_of_isIso E.hom).1
  conv_lhs => rw [hz, hc, a.hom.map_smul, E.hom.hom.map_smul]
  rw [E.hom.hom.map_smul]
  exact mul_comm c (E.hom (a (E.inv 1)))

theorem lineEndFrameScalar_app (a : L.sheaf ⟶ L.sheaf) {U : X.Opens}
    (e : L.sheaf.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (z : Γ(L.sheaf, U)) :
    a.app U z = lineEndFrameScalar L a e • z :=
  linearFrame_scalar (R := Γ(X, U)) (lineFrameAt L e le_rfl) (a.val.app (.op U)) z

theorem lineEndFrameScalar_restrict (a : L.sheaf ⟶ L.sheaf) {U V : X.Opens}
    (e : L.sheaf.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (h : V ≤ U) :
    X.presheaf.map (homOfLE h).op (lineEndFrameScalar L a e) =
      (lineFrameAt L e h).hom (a.app V ((lineFrameAt L e h).inv 1)) := by
  let F := e.inv ≫ a.over U ≫ e.hom
  let t := (SheafOfModules.unit (X.ringCatSheaf.over U)).unitHomEquiv F
  exact t.property (Over.homMk (homOfLE h) :
    Over.mk (homOfLE h) ⟶ Over.mk (𝟙 U)).op

theorem lineEndFrameScalar_app_subopen (a : L.sheaf ⟶ L.sheaf) {U V : X.Opens}
    (e : L.sheaf.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (h : V ≤ U)
    (z : Γ(L.sheaf, V)) :
    a.app V z = X.presheaf.map (homOfLE h).op (lineEndFrameScalar L a e) • z := by
  rw [lineEndFrameScalar_restrict]
  exact linearFrame_scalar (R := Γ(X, V)) (lineFrameAt L e h) (a.val.app (.op V)) z

theorem scalar_eq_of_linearFrame {R : Type u} [CommRing R] {M : ModuleCat R}
    (e : M ≅ ModuleCat.of R R)
    {r s : R} (h : ∀ z : M, r • z = s • z) : r = s := by
  have hh := congrArg e.hom (h (e.inv 1))
  have h1 : e.hom (e.inv (1 : R)) = 1 := ConcreteCategory.congr_hom e.inv_hom_id 1
  simpa only [e.hom.hom.map_smul, h1, smul_eq_mul, mul_one] using hh

theorem lineEndFrameScalar_overlap (a : L.sheaf ⟶ L.sheaf) {U V : X.Opens}
    (e : L.sheaf.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (f : L.sheaf.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V)) :
    X.presheaf.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op
        (lineEndFrameScalar L a e) =
      X.presheaf.map (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op
        (lineEndFrameScalar L a f) := by
  apply scalar_eq_of_linearFrame (R := Γ(X, U ⊓ V)) (lineFrameAt L e inf_le_left)
  intro z
  exact (lineEndFrameScalar_app_subopen L a e inf_le_left z).symm.trans
    (lineEndFrameScalar_app_subopen L a f inf_le_right z)

/-- Every endomorphism of a line bundle is multiplication by a global
regular function. Both its existence and its action on all opens are proved
by gluing the intrinsic local-frame coordinates. -/
theorem lineEnd_exists_global_scalar (a : L.sheaf ⟶ L.sheaf) :
    ∃ r : Γ(X, ⊤), ∀ (V : X.Opens) (z : Γ(L.sheaf, V)),
      a.app V z = X.presheaf.map V.leTop.op r • z := by
  let U : X → X.Opens := fun x => (L.locallyTrivial x).choose
  let e (x : X) := L.overFrameIso (U x) (L.locallyTrivial x).choose_spec.2.some
  let c : ∀ x : X, Γ(X, U x) := fun x => lineEndFrameScalar L a (e x)
  let F : TopCat.Sheaf AddCommGrpCat X :=
    ⟨(AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).presheaf, (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).isSheaf⟩
  have hcover : ∀ x : X, x ∈ U x := fun x => (L.locallyTrivial x).choose_spec.1
  have htop : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hcover x⟩
  obtain ⟨r, hr, _⟩ := F.existsUnique_gluing' U ⊤ (fun x => (U x).leTop) htop c
    (fun x y => lineEndFrameScalar_overlap L a (e x) (e y))
  change Γ(X, ⊤) at r
  refine ⟨r, ?_⟩
  intro V z
  let G : TopCat.Sheaf AddCommGrpCat X := ⟨L.sheaf.presheaf, L.sheaf.isSheaf⟩
  apply G.eq_of_locally_eq' (fun x => V ⊓ U x) V (fun _ => homOfLE inf_le_left)
  · intro x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx, hcover x⟩
  · intro x
    change L.sheaf.presheaf.map (homOfLE (show V ⊓ U x ≤ V from inf_le_left)).op
        (a.app V z) =
      L.sheaf.presheaf.map (homOfLE (show V ⊓ U x ≤ V from inf_le_left)).op
        (X.presheaf.map V.leTop.op r • z)
    calc
      _ = a.app (V ⊓ U x)
          (L.sheaf.presheaf.map (homOfLE inf_le_left).op z) :=
        (a.mapPresheaf.naturality_apply (homOfLE inf_le_left).op z).symm
      _ = X.presheaf.map (homOfLE inf_le_right).op (c x) •
          L.sheaf.presheaf.map (homOfLE inf_le_left).op z :=
        lineEndFrameScalar_app_subopen L a (e x) inf_le_right _
      _ = _ := by
        rw [Scheme.Modules.map_smul]
        congr 1
        have hx : X.presheaf.map (U x).leTop.op r = c x := hr x
        rw [← hx]
        simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LineEndScalars
