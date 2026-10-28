import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.AcyclicSideComparison
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Cochain Products -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.CochainProducts

noncomputable section

/-! Explicit products of additive cochain complexes, with their degreewise split short exact sequence and the projection comparison when the other factor is acyclic. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u

def additiveCochainProduct (C D : CochainComplex AddCommGrpCat.{u} ℕ) :
    CochainComplex AddCommGrpCat.{u} ℕ where
  X n := AddCommGrpCat.of (C.X n × D.X n)
  d i j := AddCommGrpCat.ofHom ((C.d i j).hom.prodMap (D.d i j).hom)
  shape i j hij := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · exact ConcreteCategory.congr_hom (C.shape i j hij) x.1
    · exact ConcreteCategory.congr_hom (D.shape i j hij) x.2
  d_comp_d' i j k _hij _hjk := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · exact ConcreteCategory.congr_hom (C.d_comp_d i j k) x.1
    · exact ConcreteCategory.congr_hom (D.d_comp_d i j k) x.2

def additiveCochainProductFst (C D : CochainComplex AddCommGrpCat.{u} ℕ) :
    additiveCochainProduct C D ⟶ C where
  f n := AddCommGrpCat.ofHom (AddMonoidHom.fst (C.X n) (D.X n))
  comm' _ _ _ := rfl

def additiveCochainProductInr (C D : CochainComplex AddCommGrpCat.{u} ℕ) :
    D ⟶ additiveCochainProduct C D where
  f n := AddCommGrpCat.ofHom ((0 : D.X n →+ C.X n).prod (AddMonoidHom.id _))
  comm' i j _hij := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · exact (C.d i j).hom.map_zero
    · rfl

def additiveCochainProductShortComplex (C D : CochainComplex AddCommGrpCat.{u} ℕ) :
    ShortComplex (CochainComplex AddCommGrpCat.{u} ℕ) :=
  ShortComplex.mk (additiveCochainProductInr C D) (additiveCochainProductFst C D) (by
    ext n x
    rfl)

theorem additiveCochainProduct_shortExact (C D : CochainComplex AddCommGrpCat.{u} ℕ) :
    (additiveCochainProductShortComplex C D).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have : Mono ((additiveCochainProductShortComplex C D).map
      (HomologicalComplex.eval _ (.up ℕ) n)).f :=
    (AddCommGrpCat.mono_iff_injective _).mpr (fun x y h => congrArg Prod.snd h)
  have : Epi ((additiveCochainProductShortComplex C D).map
      (HomologicalComplex.eval _ (.up ℕ) n)).g :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (fun x => ⟨(x, 0), rfl⟩)
  refine { exact := ?_ }
  rw [ShortComplex.ab_exact_iff]
  rintro ⟨x, y⟩ hx
  exact ⟨y, Prod.ext hx.symm rfl⟩

theorem additiveCochainProductFst_quasiIso
    (C D : CochainComplex AddCommGrpCat.{u} ℕ) (hD : D.Acyclic) :
    QuasiIso (additiveCochainProductFst C D) :=
  Cochain.AcyclicSideComparison.cochain_quasiIso_g_of_acyclic_first (additiveCochainProduct_shortExact C D) hD

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.CochainProducts
