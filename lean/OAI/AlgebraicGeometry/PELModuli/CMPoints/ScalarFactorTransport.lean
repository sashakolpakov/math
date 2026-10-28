import OAI.AlgebraicGeometry.PELModuli.CMPoints.Factorization
import OAI.AlgebraicGeometry.PELModuli.CMPoints.TorsionFactorIso

/-! # Scalar Factor Transport -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! Carry the actual native CM splitting to the specified abelian
schemes through group isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

def ScalarFactorTransport.groupEndConjugation {S : Scheme} {X Y : Over S} [GrpObj X] [GrpObj Y]
    (e : X ≅ Y) [IsMonHom e.hom] : (X ⟶ X) →* (Y ⟶ Y) where
  toFun f := e.inv ≫ f ≫ e.hom
  map_one' := by rw [MonObj.one_comp, MonObj.comp_one]
  map_mul' f g := by rw [MonObj.mul_comp, MonObj.comp_mul]

theorem ScalarFactorTransport.groupEndConjugation_power {S : Scheme} {X Y : Over S} [GrpObj X] [GrpObj Y]
    (e : X ≅ Y) [IsMonHom e.hom] (n : ℕ) :
    ScalarFactorTransport.groupEndConjugation e ((𝟙 X) ^ n) = (𝟙 Y) ^ n := by
  rw [map_pow]
  change (e.inv ≫ 𝟙 X ≫ e.hom) ^ n = _
  rw [Category.id_comp, e.inv_hom_id]

def HodgePiFactorization.ScalarFactorization.toAbelian
    {I : Type} [Fintype I] {A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} {B : I → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (D : HodgePiFactorization.ScalarFactorization A B)
    {g : ℕ} {d : I → ℕ} (A' : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (B' : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (d i) Foundations.Scheme.ProjectiveSpace.complexBase)
    (e : A.toOver ≅ A'.scheme) (f : ∀ i, (B i).toOver ≅ (B' i).scheme)
    (he : IsMonHom e.hom) (hf : ∀ i, IsMonHom (f i).hom) :
    TorsionFactorIso.AbelianScalarFactorization A' B' := by
  let : IsMonHom e.hom := he
  let (i : I) : IsMonHom (f i).hom := hf i
  let (i : I) : IsMonHom (D.forward i) := D.forward_group i
  let (i : I) : IsMonHom (D.backward i) := D.backward_group i
  refine {
    multiplier := D.multiplier
    positive := D.positive
    forward := fun i => e.inv ≫ D.forward i ≫ (f i).hom
    backward := fun i => (f i).inv ≫ D.backward i ≫ e.hom
    forward_group := fun _ => inferInstance
    backward_group := fun _ => inferInstance
    diagonal := ?_
    offDiagonal := ?_
    total := ?_ }
  · intro i
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (D.backward i), D.diagonal]
    exact ScalarFactorTransport.groupEndConjugation_power (f i) D.multiplier
  · intro i j hij
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (D.backward i), D.offDiagonal i j hij,
      MonObj.one_comp, MonObj.comp_one]
  · have ht i : (e.inv ≫ D.forward i ≫ (f i).hom) ≫
        ((f i).inv ≫ D.backward i ≫ e.hom) =
        ScalarFactorTransport.groupEndConjugation e (D.forward i ≫ D.backward i) := by
      simp only [ScalarFactorTransport.groupEndConjugation, MonoidHom.coe_mk, OneHom.coe_mk,
        Category.assoc, Iso.hom_inv_id_assoc]
    simp_rw [ht]
    rw [← map_prod, D.total]
    exact ScalarFactorTransport.groupEndConjugation_power e D.multiplier

def TorsionFactorIso.AbelianScalarFactorization.transport
    {S : Scheme.{0}} {I : Type} [Fintype I] {g g' : ℕ} {d d' : I → ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (d i) S}
    (D : TorsionFactorIso.AbelianScalarFactorization A B)
    (A' : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g' S) (B' : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (d' i) S)
    (e : A.scheme ≅ A'.scheme) (f : ∀ i, (B i).scheme ≅ (B' i).scheme)
    (he : IsMonHom e.hom) (hf : ∀ i, IsMonHom (f i).hom) :
    TorsionFactorIso.AbelianScalarFactorization A' B' := by
  let : IsMonHom e.hom := he
  let (i : I) : IsMonHom (f i).hom := hf i
  let (i : I) : IsMonHom (D.forward i) := D.forward_group i
  let (i : I) : IsMonHom (D.backward i) := D.backward_group i
  refine {
    multiplier := D.multiplier
    positive := D.positive
    forward := fun i => e.inv ≫ D.forward i ≫ (f i).hom
    backward := fun i => (f i).inv ≫ D.backward i ≫ e.hom
    forward_group := fun _ => inferInstance
    backward_group := fun _ => inferInstance
    diagonal := ?_
    offDiagonal := ?_
    total := ?_ }
  · intro i
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (D.backward i), D.diagonal]
    exact ScalarFactorTransport.groupEndConjugation_power (f i) D.multiplier
  · intro i j hij
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (D.backward i), D.offDiagonal i j hij,
      MonObj.one_comp, MonObj.comp_one]
  · have ht i : (e.inv ≫ D.forward i ≫ (f i).hom) ≫
        ((f i).inv ≫ D.backward i ≫ e.hom) =
        ScalarFactorTransport.groupEndConjugation e (D.forward i ≫ D.backward i) := by
      simp only [ScalarFactorTransport.groupEndConjugation, MonoidHom.coe_mk, OneHom.coe_mk,
        Category.assoc, Iso.hom_inv_id_assoc]
    simp_rw [ht]
    rw [← map_prod, D.total]
    exact ScalarFactorTransport.groupEndConjugation_power e D.multiplier

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
