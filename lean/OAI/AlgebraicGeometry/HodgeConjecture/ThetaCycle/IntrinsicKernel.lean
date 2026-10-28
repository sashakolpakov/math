import OAI.RepresentationTheory.Theta.Kernel.Intrinsic

/-! # Intrinsic Kernel -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernel.CM

/-! The complete independently checked native ThetaKernel proposition at. Its full
AdelicTheta prerequisite, actual finite inputs, tensor family, factorization,
determinant constant, and common finite-level descent are all retained. -/

abbrev NativeThetaKernelInput : Prop := RepresentationTheory.Theta.Kernel.IntrinsicCore.Intrinsic.Statement

theorem nativeThetaKernelFullInput : NativeThetaKernelInput := RepresentationTheory.Theta.Kernel.Intrinsic.theta_top_forms

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernel.CM
