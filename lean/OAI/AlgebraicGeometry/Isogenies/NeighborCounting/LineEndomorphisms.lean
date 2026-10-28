import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Line Endomorphisms -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.LineEndomorphisms

noncomputable section

/-! Endomorphisms of an actual line bundle are global scalar functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar

variable {X : Scheme.{u}} {M : X.Modules}

/-- Express a native local frame on the slice category of opens. -/
def overTrivialization (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme) :
    M.over U ≅ (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X).over U :=
  (Scheme.Modules.overEquiv U).functor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app M ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e ≪≫
      (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso U.ι).symm ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)).symm ≪≫
      ((Scheme.Modules.overFunctorEquiv U).app (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)).symm)

def overEndCoefficient (U : X.Opens)
    (q : (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X).over U ⟶ (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X).over U) : Γ(X, U) :=
  q.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))

theorem overEnd_apply (U : X.Opens)
    (q : (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X).over U ⟶ (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X).over U)
    (V : Over U) (r : Γ(X, V.left)) :
    q.val.app (op V) r = X.presheaf.map V.hom.op (overEndCoefficient U q) * r := by
  let j : V ⟶ Over.mk (𝟙 U) := Over.homMk V.hom
  have hn := (PresheafOfModules.naturality_apply q.val j.op (1 : Γ(X, U))).symm
  change X.presheaf.map V.hom.op (overEndCoefficient U q) = q.val.app (op V)
    (X.presheaf.map V.hom.op 1) at hn
  rw [map_one] at hn
  let φ : Γ(X, V.left) →ₗ[Γ(X, V.left)] Γ(X, V.left) := (q.val.app (op V)).hom
  change X.presheaf.map V.hom.op (overEndCoefficient U q) = φ 1 at hn
  have hlin : φ (r * 1) = r * φ 1 := φ.map_smul r 1
  rw [mul_one, ← hn, mul_comm] at hlin
  exact hlin

def localEndCoefficient (U : X.Opens)
    (e : M.over U ≅ (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X).over U) (q : M ⟶ M) : Γ(X, U) :=
  overEndCoefficient U (e.inv ≫ q.over U ≫ e.hom)

theorem localEndCoefficient_spec (U : X.Opens)
    (e : M.over U ≅ (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X).over U) (q : M ⟶ M)
    (V : Over U) (m : Γ(M, V.left)) :
    q.app V.left m = X.presheaf.map V.hom.op (localEndCoefficient U e q) • m := by
  let F := SheafOfModules.forget (X.ringCatSheaf.over U) ⋙
    PresheafOfModules.evaluation _ (op V)
  let eV := F.mapIso e
  let ev : Γ(M, V.left) ≃ₗ[Γ(X, V.left)] Γ(X, V.left) := eV.toLinearEquiv
  apply ev.injective
  have h := overEnd_apply U (e.inv ≫ q.over U ≫ e.hom) V (ev m)
  change ev (q.app V.left (ev.symm (ev m))) =
    X.presheaf.map V.hom.op (localEndCoefficient U e q) * ev m at h
  rw [ev.symm_apply_apply] at h
  exact h.trans (ev.map_smul
    (X.presheaf.map V.hom.op (localEndCoefficient U e q)) m).symm

theorem localScalar_faithful (U : X.Opens)
    (e : M.over U ≅ (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X).over U) (V : Over U)
    {r s : Γ(X, V.left)} (h : ∀ m : Γ(M, V.left), r • m = s • m) : r = s := by
  let F := SheafOfModules.forget (X.ringCatSheaf.over U) ⋙
    PresheafOfModules.evaluation _ (op V)
  let eV := F.mapIso e
  let ev : Γ(M, V.left) ≃ₗ[Γ(X, V.left)] Γ(X, V.left) := eV.toLinearEquiv
  have hh := congrArg ev (h (ev.symm 1))
  simpa only [ev.map_smul, ev.apply_symm_apply, smul_eq_mul, mul_one] using hh

/-- Local endomorphism coefficients agree on intersections and glue to an
actual global regular function. -/
theorem exists_scalarEnd (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) (q : M ⟶ M) :
    ∃ r : Γ(X, ⊤), ModuleScalar.scalarEnd M r = q := by
  choose U hx he using hM
  let e (x : X) := overTrivialization (U x) (Classical.choice (he x))
  let a (x : X) := localEndCoefficient (U x) (e x) q
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  have ha : TopCat.Presheaf.IsCompatible X.presheaf U a := by
    intro x y
    let Vx : Over (U x) := Over.mk (homOfLE (show U x ⊓ U y ≤ U x from inf_le_left))
    let Vy : Over (U y) := Over.mk (homOfLE (show U x ⊓ U y ≤ U y from inf_le_right))
    apply localScalar_faithful (U x) (e x) Vx
    intro m
    exact (localEndCoefficient_spec (U x) (e x) q Vx m).symm.trans
      (localEndCoefficient_spec (U y) (e y) q Vy m)
  obtain ⟨s, hs, _⟩ := X.sheaf.existsUnique_gluing' U ⊤
    (fun _ ↦ homOfLE le_top) hcover a ha
  let r : Γ(X, ⊤) := s
  have hr (x : X) : X.presheaf.map (homOfLE (show U x ≤ ⊤ from le_top)).op r = a x := hs x
  refine ⟨r, ?_⟩
  apply Scheme.Modules.hom_ext
  intro W
  ext m
  let MS : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, M.isSheaf⟩
  have hW : W ≤ iSup (fun x ↦ W ⊓ U x) := by
    intro x hxW
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW, hx x⟩
  apply MS.eq_of_locally_eq' (fun x ↦ W ⊓ U x) W
    (fun _ ↦ homOfLE inf_le_left) hW
  intro x
  let V : Over (U x) := Over.mk (homOfLE (show W ⊓ U x ≤ U x from inf_le_right))
  let j : W ⊓ U x ⟶ W := homOfLE inf_le_left
  have hn := PresheafOfModules.naturality_apply q.val j.op m
  change q.app (W ⊓ U x) (M.presheaf.map j.op m) =
    M.presheaf.map j.op (q.app W m) at hn
  have hcoeff : X.presheaf.map j.op
      (X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op r) =
      X.presheaf.map V.hom.op (a x) := by
    have h₁ := congrArg (fun f ↦ f r) (X.presheaf.map_comp
      (homOfLE (show W ≤ ⊤ from le_top)).op j.op)
    have h₂ := congrArg (fun f ↦ f r) (X.presheaf.map_comp
      (homOfLE (show U x ≤ ⊤ from le_top)).op V.hom.op)
    exact h₁.symm.trans (h₂.trans (congrArg (X.presheaf.map V.hom.op) (hr x)))
  change M.presheaf.map j.op ((ModuleScalar.scalarEnd M r).app W m) = M.presheaf.map j.op (q.app W m)
  rw [ModuleScalar.scalarEnd_apply, M.map_smul, hcoeff, ← hn]
  exact (localEndCoefficient_spec (U x) (e x) q V (M.presheaf.map j.op m)).symm

theorem scalarEnd_injective (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) : Function.Injective (ModuleScalar.scalarEnd M) := by
  intro r s h
  choose U hx he using hM
  let e (x : X) := overTrivialization (U x) (Classical.choice (he x))
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  apply X.sheaf.eq_of_locally_eq' U ⊤ (fun _ ↦ homOfLE le_top) hcover
  intro x
  apply localScalar_faithful (U x) (e x) (Over.mk (𝟙 (U x)))
  intro m
  exact congrArg (fun q : M ⟶ M ↦ q.app (U x) m) h

/-- The scalar function of a line-bundle endomorphism is unique. -/
def lineEndEquiv (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) : Γ(X, ⊤) ≃ (M ⟶ M) :=
  Equiv.ofBijective (ModuleScalar.scalarEnd M) ⟨scalarEnd_injective hM, exists_scalarEnd hM⟩

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.LineEndomorphisms
