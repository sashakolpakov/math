import OAI.AlgebraicGeometry.GroupSchemes.FiniteAlgebra
import OAI.AlgebraicGeometry.GroupSchemes.EtaleCyclic

/-! # Point Specialization -/

namespace OAI.AlgebraicGeometry.GroupSchemes

noncomputable section

/-! Specialization at a prime as an actual group homomorphism to rational points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite WithConv _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Extending rational points to any domain gives an isomorphism of point groups. -/
def FiniteEtale.FiniteCommGroupScheme.domainPointsEquiv (G : FiniteEtale.FiniteCommGroupScheme k) (S : CommAlgCat.{u} k) [IsDomain S] :
    G.rationalPoints ≃* (FiniteEtale.affine k S ⟶ G.scheme) := by
  let a : CommAlgCat.of k k ⟶ S := CommAlgCat.ofHom (Algebra.ofId k S)
  apply MulEquiv.ofBijective (G.points.map a).hom
  constructor
  · exact (G.pointMap_injective_iff a).mpr
      (FiniteAlgebra.EtaleFinite.scalar_comp_bijective k G.algebra).injective
  · intro x
    let f : G.algebra →ₐ[k] S := ((G.coordinatePoints S).symm x).ofConv
    obtain ⟨g, hg⟩ := (FiniteAlgebra.EtaleFinite.scalar_comp_bijective k G.algebra).surjective f
    refine ⟨G.coordinatePoints (CommAlgCat.of k k) (toConv g), ?_⟩
    have hx : G.coordinatePoints S (toConv f) = x := (G.coordinatePoints S).apply_symm_apply x
    exact (G.coordinatePoints_precomp a g).symm.trans
      ((congrArg (fun b => G.coordinatePoints S (toConv b)) hg).trans hx)

/-- Specialization at a prime, followed by the unique descent to the base field. -/
def FiniteEtale.FiniteCommGroupScheme.pointAtPrime (G : FiniteEtale.FiniteCommGroupScheme k) (R : CommAlgCat.{u} k) (P : PrimeSpectrum R) :
    (FiniteEtale.affine k R ⟶ G.scheme) →* G.rationalPoints :=
  (G.domainPointsEquiv (CommAlgCat.of k (R ⧸ P.asIdeal))).symm.toMonoidHom.comp
    (G.points.map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k P.asIdeal))).hom

omit [IsAlgClosed k] in
/-- Rational coordinate extraction and evaluation are inverse. -/
theorem FiniteEtale.FiniteCommGroupScheme.rationalPointsEquivAlgHom_spec (G : FiniteEtale.FiniteCommGroupScheme k) (x : G.rationalPoints) :
    G.coordinatePoints (CommAlgCat.of k k) (toConv (G.rationalPointsEquivAlgHom x)) = x :=
  (G.coordinatePoints (CommAlgCat.of k k)).apply_symm_apply x

/-- The specialized point has the same reduction modulo the prime as the original point. -/
theorem FiniteEtale.FiniteCommGroupScheme.pointAtPrime_baseChange (G : FiniteEtale.FiniteCommGroupScheme k) (R : CommAlgCat.{u} k)
    (P : PrimeSpectrum R) (x : FiniteEtale.affine k R ⟶ G.scheme) :
    (G.points.map (CommAlgCat.ofHom (Algebra.ofId k (R ⧸ P.asIdeal))))
        (G.pointAtPrime R P x) =
      (G.points.map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k P.asIdeal))) x :=
  (G.domainPointsEquiv (CommAlgCat.of k (R ⧸ P.asIdeal))).apply_symm_apply _

/-- The specialization identity in coordinate algebras. -/
theorem FiniteEtale.FiniteCommGroupScheme.pointAtPrime_coordinates (G : FiniteEtale.FiniteCommGroupScheme k) (R : CommAlgCat.{u} k)
    (P : PrimeSpectrum R) (f : G.algebra →ₐ[k] R) :
    (Ideal.Quotient.mkₐ k P.asIdeal).comp f =
      (Algebra.ofId k (R ⧸ P.asIdeal)).comp
        (G.rationalPointsEquivAlgHom (G.pointAtPrime R P (G.coordinatePoints R (toConv f)))) := by
  let x := G.coordinatePoints R (toConv f)
  let y := G.pointAtPrime R P x
  let g := G.rationalPointsEquivAlgHom y
  have hg : G.coordinatePoints (CommAlgCat.of k k) (toConv g) = y :=
    G.rationalPointsEquivAlgHom_spec y
  apply WithConv.toConv_injective
  apply (G.coordinatePoints (CommAlgCat.of k (R ⧸ P.asIdeal))).injective
  exact (G.coordinatePoints_precomp (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k P.asIdeal)) f).trans
    ((G.pointAtPrime_baseChange R P x).symm.trans
      ((congrArg (fun z => (G.points.map
        (CommAlgCat.ofHom (Algebra.ofId k (R ⧸ P.asIdeal)))) z) hg).symm.trans
          (G.coordinatePoints_precomp (CommAlgCat.ofHom (Algebra.ofId k (R ⧸ P.asIdeal))) g).symm))

/-- Specialization commutes with actual morphisms of finite group schemes. -/
theorem FiniteEtale.FiniteCommGroupScheme.pointAtPrime_postcomp {G H : FiniteEtale.FiniteCommGroupScheme k} (h : G.scheme ⟶ H.scheme)
    (R : CommAlgCat.{u} k) (P : PrimeSpectrum R) (x : FiniteEtale.affine k R ⟶ G.scheme) :
    H.pointAtPrime R P (x ≫ h) = G.pointAtPrime R P x ≫ h := by
  apply (H.domainPointsEquiv (CommAlgCat.of k (R ⧸ P.asIdeal))).injective
  change (algSpec (CommRingCat.of k)).map
      (CommAlgCat.ofHom (Algebra.ofId k (R ⧸ P.asIdeal))).op ≫ H.pointAtPrime R P (x ≫ h) =
    (algSpec (CommRingCat.of k)).map
      (CommAlgCat.ofHom (Algebra.ofId k (R ⧸ P.asIdeal))).op ≫ (G.pointAtPrime R P x ≫ h)
  have hH := H.pointAtPrime_baseChange R P (x ≫ h)
  have hG := G.pointAtPrime_baseChange R P x
  exact hH.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ h) hG.symm).trans (Category.assoc _ _ _)))

end

end OAI.AlgebraicGeometry.GroupSchemes
