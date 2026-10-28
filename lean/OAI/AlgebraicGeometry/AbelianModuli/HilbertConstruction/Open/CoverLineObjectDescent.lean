import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.ObjectDescent

/-! # Cover Line Object Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.CoverLineObjectDescent.OpenCoverLineObjectDescent

noncomputable section

/-! Native line objects descend on arbitrary scheme open covers. The
cover is replaced by its literal image opens through the original
open-immersion isomorphisms; recovery returns the given chart sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {X : Scheme.{u}} (C : X.OpenCover.{u})
  (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData C.f)

def imageOpen (i : C.I₀) : X.Opens := (C.f i).opensRange

def imageIso (i : C.I₀) : C.X i ≅ (imageOpen C i).toScheme :=
  IsOpenImmersion.isoOfRangeEq (C.f i) (imageOpen C i).ι (by
    rw [Scheme.Opens.range_ι]
    rfl)

theorem imageIso_hom_fac (i : C.I₀) : (imageIso C i).hom ≫ (imageOpen C i).ι = C.f i :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem imageIso_inv_fac (i : C.I₀) : (imageIso C i).inv ≫ C.f i = (imageOpen C i).ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

theorem imageOpen_covers (x : X) : ∃ i, x ∈ imageOpen C i := by
  obtain ⟨i, y, rfl⟩ := C.exists_eq x
  exact ⟨i, ⟨y, rfl⟩⟩

def literalDatum : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun i => (imageOpen C i).ι) :=
  Pseudofunctor.DescentData.pullFunctorObj
    (p := 𝟙 X) (α := id) (p' := fun i => (imageIso C i).inv)
    (fun i => (imageIso_inv_fac C i).trans (Category.comp_id _).symm) D

variable (hD : ∀ i, Picard.PoincareBundle.Line.Bundles.IsLine (D.obj i))

include hD in
theorem literalDatum_isLine (i : C.I₀) :
    Picard.PoincareBundle.Line.Bundles.IsLine ((literalDatum C D).obj i) :=
  (hD i).pullback (imageIso C i).inv

/-- The line object is constructed by native module descent and keeps
the exact original sheaf after pullback to every member of the cover. -/
def lineBundle : Line.Bundles.LineBundle X :=
  OpenModule.ObjectDescent.OpenModuleObjectDescent.lineBundle (imageOpen C) (literalDatum C D)
    (imageOpen_covers C) (literalDatum_isLine C D hD)

def imageRecovery (i : C.I₀) :
    ((lineBundle C D hD).pullback (imageOpen C i).ι).sheaf ≅
      (Scheme.Modules.pullback (imageIso C i).inv).obj (D.obj i) :=
  OpenModule.ObjectDescent.OpenModuleObjectDescent.lineBundle_recovery (imageOpen C) (literalDatum C D)
    (imageOpen_covers C) (literalDatum_isLine C D hD) i

def recovery (i : C.I₀) : ((lineBundle C D hD).pullback (C.f i)).sheaf ≅ D.obj i :=
  (Scheme.Modules.pullbackCongr (imageIso_hom_fac C i).symm).app (lineBundle C D hD).sheaf ≪≫
    (Scheme.Modules.pullbackComp (imageIso C i).hom (imageOpen C i).ι).symm.app (lineBundle C D hD).sheaf ≪≫
    (Scheme.Modules.pullback (imageIso C i).hom).mapIso (imageRecovery C D hD i) ≪≫
    (Scheme.Modules.pullbackComp (imageIso C i).hom (imageIso C i).inv).app (D.obj i) ≪≫
    (Scheme.Modules.pullbackCongr (imageIso C i).hom_inv_id).app (D.obj i) ≪≫
    (Scheme.Modules.pullbackId (C.X i)).app (D.obj i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.CoverLineObjectDescent.OpenCoverLineObjectDescent
