import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleQuasicoherent
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Integral Line Bundle Sections -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.IntegralLineBundleSections.Construction

noncomputable section

/-! Sections of a line bundle on an integral scheme are detected on any nonempty open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

def overFrameOnOpenLinearEquiv {X : Scheme.{u}} {M : X.Modules} {W : X.Opens}
    (e : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    {U : X.Opens} (hU : U ≤ W) : Γ(M, U) ≃ₗ[Γ(X, U)] Γ(X, U) :=
  ((SheafOfModules.evaluation (X.ringCatSheaf.over W)
    (.op (Over.mk (homOfLE hU)))).mapIso e).toLinearEquiv

theorem overFrameOnOpenLinearEquiv_restrict
    {X : Scheme.{u}} {M : X.Modules} {W : X.Opens}
    (e : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    {U V : X.Opens} (h : V ≤ U) (hU : U ≤ W) (s : Γ(M, U)) :
    X.presheaf.map (homOfLE h).op (overFrameOnOpenLinearEquiv e hU s) =
      overFrameOnOpenLinearEquiv e (h.trans hU) (M.presheaf.map (homOfLE h).op s) := by
  let a : Over.mk (homOfLE (h.trans hU)) ⟶ Over.mk (homOfLE hU) :=
    Over.homMk (homOfLE h)
  exact (PresheafOfModules.naturality_apply e.hom.val a.op s).symm

theorem framed_section_restriction_injective
    {X : Scheme.{u}} [IsIntegral X] {M : X.Modules} {W : X.Opens}
    (e : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    {U V : X.Opens} [Nonempty V] (h : V ≤ U) (hU : U ≤ W) :
    Function.Injective (M.presheaf.map (homOfLE h).op) := by
  intro s t hst
  apply (overFrameOnOpenLinearEquiv e hU).injective
  apply map_injective_of_isIntegral X (homOfLE h)
  rw [overFrameOnOpenLinearEquiv_restrict e h hU,
    overFrameOnOpenLinearEquiv_restrict e h hU, hst]

theorem lineBundle_section_restriction_injective
    {X : Scheme.{u}} [IsIntegral X] (M : X.Modules) (hM : LineBundle.Construction.IsLineBundle M)
    {U V : X.Opens} [Nonempty V] (h : V ≤ U) :
    Function.Injective (M.presheaf.map (homOfLE h).op) := by
  choose W hx e using hM
  let E (x : X) := LineBundleQuasicoherent.Construction.lineBundleOverTrivialization (W x) (e x).some
  have hηV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
  have hηW (x : X) : genericPoint X ∈ W x :=
    ((genericPoint_spec X).mem_open_set_iff (W x).isOpen).mpr
      ⟨x, Set.mem_univ x, hx x⟩
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨M.presheaf, M.isSheaf⟩
  intro s t hst
  apply F.eq_of_locally_eq' (fun x => U ⊓ W x) U (fun _ => homOfLE inf_le_left)
    (by intro x hxU; exact Opens.mem_iSup.mpr ⟨x, hxU, hx x⟩) s t
  intro x
  let Z : X.Opens := V ⊓ (U ⊓ W x)
  have : Nonempty Z := ⟨⟨genericPoint X, hηV, h hηV, hηW x⟩⟩
  apply framed_section_restriction_injective (E x)
    (show Z ≤ U ⊓ W x from inf_le_right) inf_le_right
  have hh := congrArg (fun z : Γ(M, V) =>
    M.presheaf.map (homOfLE (show Z ≤ V from inf_le_left)).op z) hst
  dsimp only [F]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hh ⊢
  exact hh

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.IntegralLineBundleSections.Construction
