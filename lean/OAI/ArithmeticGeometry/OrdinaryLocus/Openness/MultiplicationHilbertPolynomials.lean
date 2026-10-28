import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AmpleHilbert
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationHilbertSections
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FinitePushforward
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.EventualPolynomialIdentity

/-! # Multiplication Hilbert Polynomials -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationHilbertPolynomials.Construction

noncomputable section

/-! Actual Hilbert polynomials for a symmetric ample bundle and its multiplication pushforward. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {K : Type} [Field K] [IsAlgClosed K]
variable (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

theorem exists_multiplication_Hilbert_polynomials (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (hL : L.IsAmple)
    (hs : Nonempty ((L.pullback ((𝟙 A : A ⟶ A)⁻¹).left).sheaf ≅ L.sheaf))
    (m : ℕ) (hm : 0 < m) [IsFinite (Multiplication.Construction.multiplicationMap A m).left] :
    ∃ (d : ℕ), 0 < d ∧ ∃ (P Q : Polynomial ℚ) (b : ℕ),
      (∀ n : ℕ, b ≤ n →
        (Module.finrank Γ(Spec (.of K), ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor A.hom).obj
          (L.tensorPower (n * d)).sheaf) : ℚ) = P.eval (n : ℚ)) ∧
      (∀ n : ℕ, b ≤ n →
        (Module.finrank Γ(Spec (.of K), ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor A.hom).obj
          (SheafTensor.Construction.sheafTensor ((Scheme.Modules.pushforward (Multiplication.Construction.multiplicationMap A m).left).obj
            (LineBundle.Construction.structureSheafModule A.left)) (L.tensorPower (n * d)).sheaf)) : ℚ) = Q.eval (n : ℚ)) ∧
      Q = P.comp (Polynomial.X * Polynomial.C ((m ^ 2 : ℕ) : ℚ)) := by
  let : Field Γ(Spec (.of K), ⊤) := AlgebraicGeometry.Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField K
  let O := LineBundle.Construction.structureSheafModule A.left
  have : O.IsQuasicoherent := AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial A.left)
  have : O.IsFinitePresentation :=
    AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial A.left)
  have : O.IsFiniteType := by
    obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData O
    refine { exists_localGeneratorsData := ⟨q.localGeneratorsData, ?_⟩ }
    constructor
    intro i
    exact (hq.isFinite_presentation i).isFiniteType_generators
  let F := (Scheme.Modules.pushforward (Multiplication.Construction.multiplicationMap A m).left).obj O
  have : F.IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom _
  have : F.IsFiniteType := FinitePushforward.Construction.finitePushforward_isFiniteType _ O
  obtain ⟨d, hd, r, hp⟩ := AmpleHilbert.Construction.ample_sections_eventuallyPolynomial A.hom (Field.toIsField _) L hL
  obtain ⟨P, _, bP, hP⟩ := hp O
  obtain ⟨Q, _, bQ, hQ⟩ := hp F
  have hP' (n : ℕ) (hn : bP ≤ n) :
      (Module.finrank Γ(Spec (.of K), ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor A.hom).obj
        (L.tensorPower (n * d)).sheaf) : ℚ) = P.eval (n : ℚ) := by
    have he := ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor A.hom).mapIso
      (SheafTensor.Construction.sheafTensorUnitLeft (L.tensorPower (n * d)).sheaf)).toLinearEquiv.finrank_eq
    exact (congrArg (fun k : ℕ => (k : ℚ)) he).symm.trans (hP n hn)
  refine ⟨d, hd, P, Q, max bP bQ,
    fun n hn => hP' n ((le_max_left _ _).trans hn),
    fun n hn => hQ n ((le_max_right _ _).trans hn), ?_⟩
  apply EventualPolynomialIdentity.Construction.polynomial_comp_mul_of_eventually_eval P Q (m ^ 2) (max bP bQ)
  intro n hn
  have hnm : n ≤ n * m ^ 2 := Nat.le_mul_of_pos_right n (pow_pos hm 2)
  have he := congrArg (fun k : ℕ => (k : ℚ))
    (MultiplicationHilbertSections.Construction.multiplication_pushforward_sections_finrank A L hs m (n * d))
  have hpow : (n * d) * m ^ 2 = (n * m ^ 2) * d := by ac_rfl
  rw [hpow] at he
  exact (hQ n ((le_max_right _ _).trans hn)).symm.trans
    (he.trans (hP' (n * m ^ 2) (((le_max_left _ _).trans hn).trans hnm)))

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationHilbertPolynomials.Construction
