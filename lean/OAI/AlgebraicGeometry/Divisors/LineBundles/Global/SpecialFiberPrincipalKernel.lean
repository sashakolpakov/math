import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.KernelAffineImage
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SpecialFiberPrincipalKernel
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.Specialization

/-! # Special Fiber Principal Kernel -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecialFiberPrincipalKernel.BundleCycles

noncomputable section

/-! The actual global deformation parameter generates the scheme-theoretic special-fiber kernel on every affine deformation chart image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme.{0}} (I : X.IdealSheafData)

theorem globalSpecialFiber_kernel_on_chart (U : X.AffineZariskiSite) :
    RingHom.ker (Spec.map ((SpecialFiber.BundleCycles.deformationToSpecialDiagram I).app (.op U))).appTop.hom =
    Ideal.span {((Deformation.BundleCycles.globalDeformationCover I).f U).appTop (Specialization.BundleCycles.globalDeformationParameterSection I)} := by
  have h := Affine.SpecialFiberPrincipalKernel.BundleCycles.affineSpecialFiber_principal_kernel (I.ideal U)
  have he := Specialization.BundleCycles.globalDeformationParameterSection_on_chart I U
  exact h.trans (congrArg (fun t : Γ((Deformation.BundleCycles.globalDeformationCover I).X U, ⊤) => Ideal.span {t}) he.symm)

theorem globalSpecialFiber_kernel_on_affineImage (U : X.AffineZariskiSite) :
    RingHom.ker ((SpecialFiber.BundleCycles.globalSpecialFiberMap I).app
      ((Deformation.BundleCycles.globalDeformationCover I).f U ''ᵁ (⊤ : ((Deformation.BundleCycles.globalDeformationCover I).X U).Opens))).hom =
    Ideal.span {(Deformation.BundleCycles.globalDeformation I).presheaf.map
      (homOfLE (show (Deformation.BundleCycles.globalDeformationCover I).f U ''ᵁ (⊤ : ((Deformation.BundleCycles.globalDeformationCover I).X U).Opens) ≤ ⊤ from le_top)).op
      (Specialization.BundleCycles.globalDeformationParameterSection I)} :=
  Principal.KernelAffineImage.BundleCycles.principalKernel_on_affineImage (SpecialFiber.BundleCycles.globalSpecialFiberMap I) ((Deformation.BundleCycles.globalDeformationCover I).f U)
    ((SpecialFiber.BundleCycles.globalSpecialFiberCover I).f U)
    (Spec.map ((SpecialFiber.BundleCycles.deformationToSpecialDiagram I).app (.op U)))
    (SpecialFiber.BundleCycles.globalSpecialFiberMap_chart_isPullback I U) (Specialization.BundleCycles.globalDeformationParameterSection I)
    (globalSpecialFiber_kernel_on_chart I U)

theorem globalSpecialFiber_exists_principal_affineNeighborhood (x : Deformation.BundleCycles.globalDeformation I) :
    ∃ (U : (Deformation.BundleCycles.globalDeformation I).Opens), IsAffineOpen U ∧ x ∈ U ∧
      RingHom.ker ((SpecialFiber.BundleCycles.globalSpecialFiberMap I).app U).hom =
        Ideal.span {(Deformation.BundleCycles.globalDeformation I).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
          (Specialization.BundleCycles.globalDeformationParameterSection I)} := by
  obtain ⟨V, y, rfl⟩ := (Deformation.BundleCycles.globalDeformationCover I).exists_eq x
  let : IsAffine ((Deformation.BundleCycles.globalDeformationCover I).X V) := DeformationProperties.BundleCycles.globalDeformationCover_isAffine I V
  let : IsOpenImmersion ((Deformation.BundleCycles.globalDeformationCover I).f V) := DeformationProperties.BundleCycles.globalDeformationCover_isOpenImmersion I V
  refine ⟨(Deformation.BundleCycles.globalDeformationCover I).f V ''ᵁ (⊤ : ((Deformation.BundleCycles.globalDeformationCover I).X V).Opens),
    (isAffineOpen_top ((Deformation.BundleCycles.globalDeformationCover I).X V)).image_of_isOpenImmersion _, ⟨y, trivial, rfl⟩, ?_⟩
  exact globalSpecialFiber_kernel_on_affineImage I V

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecialFiberPrincipalKernel.BundleCycles
