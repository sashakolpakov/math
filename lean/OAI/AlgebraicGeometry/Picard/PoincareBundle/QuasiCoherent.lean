import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles

/-! # Quasi Coherent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.QuasiCoherent

noncomputable section

/-!
# Quasi-coherence of the geometric line bundles used for PoincareBundle

Local isomorphisms with the structure sheaf give quasi-coherence by the
local presentation criterion. No quasi-coherence assumption is added to
the definition of a line bundle.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

/-- A geometric trivialization also trivializes the sheaf on the slice site. -/
def overTrivialization {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Line.Bundles.unitLine U) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app M ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e ≪≫
      (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf).symm)

/-- The structure sheaf on a slice site has a singleton free presentation. -/
theorem unitOver_isQuasicoherent {X : Scheme.{u}} (U : X.Opens) :
    (SheafOfModules.unit (X.ringCatSheaf.over U)).IsQuasicoherent := by
  let e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit.{u + 1} ≅
      SheafOfModules.unit (X.ringCatSheaf.over U) :=
    coproductUniqueIso _
  exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U)).prop_of_iso e inferInstance

/-- Every locally trivial rank-one module sheaf is quasi-coherent. -/
theorem isQuasicoherent_of_isLine {X : Scheme.{u}} (M : X.Modules)
    (hM : Line.Bundles.IsLine M) : M.IsQuasicoherent := by
  classical
  choose U hx he using hM
  have hcover : (Opens.grothendieckTopology X).CoversTop U := by
    rw [Opens.coversTop_iff, TopologicalSpace.IsOpenCover]
    apply top_le_iff.mp
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  have : ∀ x, (M.over (U x)).IsQuasicoherent := fun x =>
    (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over (U x))).prop_of_iso
      (overTrivialization M (U x) (he x).some).symm (unitOver_isQuasicoherent (U x))
  exact SheafOfModules.IsQuasicoherent.of_coversTop M U hcover

instance {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) : L.sheaf.IsQuasicoherent :=
  isQuasicoherent_of_isLine L.sheaf L.isLine

/-- On an affine scheme a geometric line bundle is recovered from its
module of global sections. -/
def affineTildeIso {R : CommRingCat.{u}} (L : Line.Bundles.LineBundle (Spec R)) :
    tilde ((moduleSpecΓFunctor (R := R)).obj L.sheaf) ≅ L.sheaf := by
  have : L.sheaf.IsQuasicoherent := isQuasicoherent_of_isLine L.sheaf L.isLine
  let f : tilde ((moduleSpecΓFunctor (R := R)).obj L.sheaf) ⟶ L.sheaf :=
    Scheme.Modules.fromTildeΓ (R := R) L.sheaf
  have hf : IsIso f :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) L.sheaf
  exact @asIso _ _ _ _ f hf

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.QuasiCoherent
