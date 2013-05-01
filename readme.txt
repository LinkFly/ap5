1. Into "initial commit" ap5 sources exactly from ap5-20120509.zip.

Patches.
1. lispworks:without-preemption changed to system:with-other-threads-disabled
	This is temporary decision. From lispworks manual: "with-other-threads-disabled cannot be guaranteed to be 100% safe in all cases, and therefore must not be used in end-user applications. It is useful for debugging purposes."


