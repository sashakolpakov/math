import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LineEndScalars
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleGluingIs

/-! # Local Line Iso Gluing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LocalLineIsoGluing

noncomputable section

/-! Compatible isomorphisms on local line-bundle frames glue to an
actual global isomorphism of their module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u
variable {X : Scheme.{u}}

def localModuleIsoAt {L M : X.Modules} {U : X.Opens}
    (e : L.over U ≅ M.over U) {V : X.Opens} (h : V ≤ U) :
    L.val.obj (.op V) ≅ M.val.obj (.op V) :=
  (SheafOfModules.evaluation (X.ringCatSheaf.over U)
    (.op (Over.mk (homOfLE h)))).mapIso e

/-- The gluing theorem retains the actual local isomorphism on every
smaller open, not just its isomorphism class. -/
theorem local_module_isos_glue (L M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (e : ∀ i, L.over (U i) ≅ M.over (U i))
    (he : ∀ i j (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
      (localModuleIsoAt (e i) hi).hom = (localModuleIsoAt (e j) hj).hom) :
    ∃ a : L ≅ M, ∀ i, a.hom.over (U i) = (e i).hom := by
  let D : Quotients.FiniteDescent.ModuleGluingIs.Construction.ModuleGluing.Datum L M := {
    I := ι
    opens := U
    covers := hU
    app := fun i V h => (localModuleIsoAt (e i) h).hom.hom
    naturality := fun i V W h hV s => by
      exact (PresheafOfModules.naturality_apply (e i).hom.val
        (Over.homMk (homOfLE h) : Over.mk (homOfLE (h.trans hV)) ⟶
          Over.mk (homOfLE hV)).op s).symm
    overlap := fun i j V hi hj => congrArg ModuleCat.Hom.hom (he i j V hi hj) }
  have hD : IsIso D.glue := D.glue_isIso (fun i V h =>
    ConcreteCategory.bijective_of_isIso (localModuleIsoAt (e i) h).hom)
  refine ⟨asIso D.glue, ?_⟩
  intro i
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext s
  exact D.glue_spec i V.unop.left V.unop.hom.le s

/-- An isomorphism on an open subscheme transports to its slice site. -/
def localLineIsoOver (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (U : X.Opens)
    (e : (L.pullback U.ι).sheaf ≅ (M.pullback U.ι).sheaf) :
    L.sheaf.over U ≅ M.sheaf.over U :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso <|
    (Scheme.Modules.overFunctorEquiv U).app L.sheaf ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app L.sheaf ≪≫ e ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M.sheaf).symm ≪≫
    ((Scheme.Modules.overFunctorEquiv U).app M.sheaf).symm

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LocalLineIsoGluing
