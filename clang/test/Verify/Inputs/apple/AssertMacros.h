// The part of Apple's <AssertMacros.h> that collides with cppverify::check:
// unless __ASSERT_MACROS_DEFINE_VERSIONS_WITHOUT_UNDERSCORES is 0, it defines
// check(assertion) as __Check(assertion), which production code defines empty.

#ifndef __ASSERT_MACROS_DEFINE_VERSIONS_WITHOUT_UNDERSCORES
#define __ASSERT_MACROS_DEFINE_VERSIONS_WITHOUT_UNDERSCORES 1
#endif

#define __Check(assertion)

#if __ASSERT_MACROS_DEFINE_VERSIONS_WITHOUT_UNDERSCORES
#ifndef check
#define check(assertion) __Check(assertion)
#endif
#endif
