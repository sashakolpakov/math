import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechExact

/-! # Ordered Cech -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCech.Comparison

noncomputable section

/-! The supported Čech comparison and its canonical support-forgetting
map, once the positive rows of the chosen resolution are exact. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z
variable (R : Type u) [CommRing R] (X : TopCat.{v})
  {C : Type w} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) {ι : Type w} [LinearOrder ι] (U : ι → C) (O : Opens X)
  (K : CochainComplex (Sheaf (Opens.grothendieckTopology X)
    (ModuleCat.{max u v w z} R)) ℕ)
  (hO : ∀ i, F.obj (U i) ≤ O)
  (hcover : F.obj (⊤_ C) ⊓ O ≤ ⨆ i, F.obj (U i))
  (hrows : ∀ q r,
    ((OrderedCechEdge.bicomplex.{u,v,w,z} R X F U K).X q).ExactAt (r + 1))

local notation "V" => F.obj (⊤_ C)

local instance total_exists :
    (OrderedCechEdge.bicomplex.{u,v,w,z} R X F U K).HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts _

include hcover hrows in
theorem quasiIso : QuasiIso (OrderedCechEdge.map.{u,v,w,z} R X F U O K hO) :=
  GeometricComparison.Module.TotalEdge.ModuleTotalEdge.quasiIso.{u,max v w z} R
    (OrderedCechEdge.bicomplex.{u,v,w,z} R X F U K)
    (OrderedCechEdge.source.{u,v,w,z} R X F O K)
    (OrderedCechEdge.component.{u,v,w,z} R X F U O K)
    (fun q q' _ => OrderedCechEdge.comm.{u,v,w,z} R X F U O K q q')
    (OrderedCechEdge.cocycle.{u,v,w,z} R X F U O K hO)
    (OrderedCechExact.exact.{u,v,w,z} R X F U O K hO hcover)
    (OrderedCechExact.mono.{u,v,w,z} R X F U O K) hrows

def homologyIso (i : ℕ) :
    (OrderedCechEdge.source.{u,v,w,z} R X F O K).homology i ≅
      ((OrderedCechEdge.bicomplex.{u,v,w,z} R X F U K).total (.up ℕ)).homology i := by
  letI := quasiIso.{u,v,w,z} R X F U O K hO hcover hrows
  exact isoOfQuasiIsoAt (OrderedCechEdge.map.{u,v,w,z} R X F U O K hO) i

def forgetSupport (hglobal : V ⊔ O = ⊤) (i : ℕ) :
    ((OrderedCechEdge.bicomplex.{u,v,w,z} R X F U K).total (.up ℕ)).homology i ⟶
      (((SectionsExcision.sections (D := ModuleCat.{max u v w z} R)
        (⊤ : Opens X)).mapHomologicalComplex (.up ℕ)).obj K).homology i :=
  (homologyIso.{u,v,w,z} R X F U O K hO hcover hrows i).inv ≫
    HomologicalComplex.homologyMap
      (SectionsExcision.extensionComplex O V hglobal K) i

theorem map_forgetSupport (hglobal : V ⊔ O = ⊤) (i : ℕ) :
    HomologicalComplex.homologyMap
      (OrderedCechEdge.map.{u,v,w,z} R X F U O K hO) i ≫
        forgetSupport.{u,v,w,z} R X F U O K hO hcover hrows hglobal i =
    HomologicalComplex.homologyMap
      (SectionsExcision.extensionComplex O V hglobal K) i := by
  change (homologyIso.{u,v,w,z} R X F U O K hO hcover hrows i).hom ≫
    ((homologyIso.{u,v,w,z} R X F U O K hO hcover hrows i).inv ≫ _) = _
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCech.Comparison
