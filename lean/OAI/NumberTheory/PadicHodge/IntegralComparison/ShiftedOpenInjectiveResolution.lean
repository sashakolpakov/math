import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.OpenInjectiveResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Extension

/-! # Shifted Open Injective Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ShiftedOpenInjectiveResolution

noncomputable section

/-! The original single coefficient sheaf maps to its chosen injective
resolution shifted into the same nonnegative degree. On acyclic opens
this actual map is a quasi-isomorphism, naturally for coefficient maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.OpenInjectiveResolution
variable {X : TopCat.{u}} (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (c : ℕ)

abbrev shape := CohomologyConcentration.shift c

def complex := (Acyclic.OpenInjectiveResolution.resolution F).cocomplex.extend (shape c)

def sourceIso : ((CochainComplex.single₀ _).obj F).extend (shape c) ≅
    (single _ (.up ℕ) c).obj F :=
  extendSingleIso (shape c) F 0 c (by simp [shape, CohomologyConcentration.shift])

def augmentation : (single _ (.up ℕ) c).obj F ⟶ complex F c :=
  (sourceIso F c).inv ≫ extendMap (Acyclic.OpenInjectiveResolution.resolution F).ι (shape c)

variable {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (f : F ⟶ G)

def map : complex F c ⟶ complex G c :=
  extendMap (InjectiveResolution.desc f (Acyclic.OpenInjectiveResolution.resolution G) (Acyclic.OpenInjectiveResolution.resolution F)) (shape c)

theorem sourceIso_naturality :
    (sourceIso F c).inv ≫ extendMap ((CochainComplex.single₀ _).map f) (shape c) =
      (single _ (.up ℕ) c).map f ≫ (sourceIso G c).inv := by
  apply from_single_hom_ext
  simp only [comp_f, sourceIso, extendSingleIso_inv_f,
    extendMap_f _ _ (show (shape c).f 0 = c by simp [shape, CohomologyConcentration.shift]),
    single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc]

theorem naturality : augmentation F c ≫ ShiftedOpenInjectiveResolution.map F c f =
    (single _ (.up ℕ) c).map f ≫ augmentation G c := by
  dsimp only [augmentation, ShiftedOpenInjectiveResolution.map]
  rw [Category.assoc, ← extendMap_comp, InjectiveResolution.desc_commutes,
    extendMap_comp, ← Category.assoc, sourceIso_naturality, Category.assoc]

private theorem flasque_of_iso
    {P Q : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (e : P ≅ Q) [TopCat.Sheaf.IsFlasque Q] : TopCat.Sheaf.IsFlasque P where
  epi {U V} j := by
    have h : Epi (P.obj.map j ≫ e.hom.hom.app V) := by
      rw [e.hom.hom.naturality]
      infer_instance
    exact (epi_comp_iff_of_isIso (P.obj.map j) (e.hom.hom.app V)).mp h

theorem term_flasque (q : ℕ) : TopCat.Sheaf.IsFlasque ((complex F c).X q) := by
  classical
  by_cases h : ∃ i, (shape c).f i = q
  · obtain ⟨i, hi⟩ := h
    let : TopCat.Sheaf.IsFlasque ((Acyclic.OpenInjectiveResolution.resolution F).cocomplex.X i) :=
      @AlgebraicGeometry.SheafCohomology.Cech.Compat.TopCat.Sheaf.IsFlasque.of_injective X _ ((Acyclic.OpenInjectiveResolution.resolution F).injective i)
    exact flasque_of_iso ((Acyclic.OpenInjectiveResolution.resolution F).cocomplex.extendXIso (shape c) hi)
  · have hz : IsZero ((complex F c).X q) :=
      (Acyclic.OpenInjectiveResolution.resolution F).cocomplex.isZero_extend_X (shape c) q (fun i hi => h ⟨i, hi⟩)
    constructor
    intro U V j
    exact ((Acyclic.OpenInjectiveResolution.sections V.unop).map_isZero hz).epi (((complex F c).X q).obj.map j)

variable (U : Opens X)
  (hF : ∀ q, Subsingleton (CategoryTheory.Sheaf.H
    ((AlgebraicGeometry.SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat U.isOpenEmbedding).obj F) (q+1)))

include hF in
theorem sections_quasiIso : QuasiIso
    (((Acyclic.OpenInjectiveResolution.sections U).mapHomologicalComplex (.up ℕ)).map (augmentation F c)) := by
  let : QuasiIso (((Acyclic.OpenInjectiveResolution.sections U).mapHomologicalComplex (.up ℕ)).map (Acyclic.OpenInjectiveResolution.resolution F).ι) :=
    Acyclic.OpenInjectiveResolution.mapped_quasiIso F U hF
  have hq : QuasiIso
      (((Acyclic.OpenInjectiveResolution.sections U).mapHomologicalComplex (.up ℕ)).map (extendMap (Acyclic.OpenInjectiveResolution.resolution F).ι (shape c)) ≫
        (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso (Acyclic.OpenInjectiveResolution.sections U) (shape c) (Acyclic.OpenInjectiveResolution.resolution F).cocomplex).hom) := by
    rw [AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso_naturality]
    infer_instance
  have : QuasiIso
      (((Acyclic.OpenInjectiveResolution.sections U).mapHomologicalComplex (.up ℕ)).map (extendMap (Acyclic.OpenInjectiveResolution.resolution F).ι (shape c))) :=
    quasiIso_of_comp_right _
      (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso (Acyclic.OpenInjectiveResolution.sections U) (shape c) (Acyclic.OpenInjectiveResolution.resolution F).cocomplex).hom
      (hφφ' := hq)
  dsimp only [augmentation]
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ShiftedOpenInjectiveResolution
