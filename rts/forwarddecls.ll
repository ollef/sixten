declare i8* @GC_malloc(i64)
declare void @GC_init()
declare void @exit(i32)
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* nocapture, i8* nocapture readonly, i64, i32, i1) #0
declare void @llvm.memcpy.p0i8.p0i8.i32(i8* nocapture, i8* nocapture readonly, i32, i32, i1) #0
@hello1 = private constant [7 x i8] c"hello1\00"
@hello2 = private constant [7 x i8] c"hello2\00"
@hello3 = private constant [7 x i8] c"hello3\00"
@hello4 = private constant [7 x i8] c"hello4\00"
declare i32 @puts(i8* nocapture) nounwind
; call i32 @puts(i8* getelementptr inbounds ([7 x i8], [7 x i8]* @hello1, i64 0, i64 0))
@size_t-format = private constant [5 x i8] c"%zd\0A\00"
declare i32 @printf(i8* noalias nocapture, ...)
