mod flush;
mod write;
mod write_all;
mod write_fmt;
mod write_vectored;

use flush::FlushFuture;
use write::WriteFuture;
use write_all::WriteAllFuture;
use write_fmt::WriteFmtFuture;
use write_vectored::WriteVectoredFuture;

use crate::io::{self, IoSlice};

extension_trait! {
    use std::pin::Pin;
    use std::ops::{Deref, DerefMut};

    use crate::task::{Context, Poll};

    #[doc = r#"
        Allows writing to a byte stream.

        This trait is a re-export of [`futures::io::AsyncWrite`] and is an async version of
        [`std::io::Write`].

        Methods other than [`poll_write`], [`poll_write_vectored`], [`poll_flush`], and
        [`poll_close`] do not really exist in the trait itself, but they become available when
        [`WriteExt`] from the [prelude] is imported:

        ```
        # #[allow(unused_imports)]
        use async_std::prelude::*;
        ```

        [`std::io::Write`]: https://doc.rust-lang.org/std/io/trait.Write.html
        [`futures::io::AsyncWrite`]:
        https://docs.rs/futures/0.3/futures/io/trait.AsyncWrite.html
        [`poll_write`]: #tymethod.poll_write
        [`poll_write_vectored`]: #method.poll_write_vectored
        [`poll_flush`]: #tymethod.poll_flush
        [`poll_close`]: #tymethod.poll_close
        [`WriteExt`]: ../io/prelude/trait.WriteExt.html
        [prelude]: ../prelude/index.html
    "#]
    pub trait Write {
        #[doc = r#"
            Attempt to write bytes from `buf` into the object.
        "#]
        fn poll_write(
            self: Pin<&mut Self>,
            cx: &mut Context<'_>,
            buf: &[u8],
        ) -> Poll<io::Result<usize>>;

        #[doc = r#"
            Attempt to write bytes from `bufs` into the object using vectored IO operations.
        "#]
        fn poll_write_vectored(
            self: Pin<&mut Self>,
            cx: &mut Context<'_>,
            bufs: &[IoSlice<'_>]
        ) -> Poll<io::Result<usize>> {
            unreachable!("this impl only appears in the rendered docs")
        }

        #[doc = r#"
            Attempt to flush the object, ensuring that any buffered data reach
            their destination.
        "#]
        fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>>;

        #[doc = r#"
            Attempt to close the object.
        "#]
        fn poll_close(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>>;
    }

    #[doc = r#"
        Extension methods for [`Write`].

        [`Write`]: ../trait.Write.html
    "#]
    pub trait WriteExt: futures_io::AsyncWrite {
        #[doc = r#"
            Writes some bytes into the byte stream.

            Returns the number of bytes written from the start of the buffer.

            If the return value is `Ok(n)` then it must be guaranteed that
            `0 <= n <= buf.len()`. A return value of `0` typically means that the underlying
            object is no longer able to accept bytes and will likely not be able to in the
            future as well, or that the buffer provided is empty.

            # Examples

            ```no_run
            # fn main() -> std::io::Result<()> { async_std::task::block_on(async {
            #
            use async_std::fs::File;
            use async_std::prelude::*;

            let mut file = File::create("a.txt").await?;

            let n = file.write(b"hello world").await?;
            #
            # Ok(()) }) }
            ```
        "#]
        fn write<'a>(
            &'a mut self,
            buf: &'a [u8],
        ) -> impl Future<Output = io::Result<usize>> + 'a [WriteFuture<'a, Self>]
        where
            Self: Unpin,
        {
            WriteFuture { writer: self, buf }
        }

        #[doc = r#"
            Flushes the stream to ensure that all buffered contents reach their destination.

            # Examples

            ```no_run
            # fn main() -> std::io::Result<()> { async_std::task::block_on(async {
            #
            use async_std::fs::File;
            use async_std::prelude::*;

            let mut file = File::create("a.txt").await?;

            file.write_all(b"hello world").await?;
            file.flush().await?;
            #
            # Ok(()) }) }
            ```
        "#]
        fn flush(&mut self) -> impl Future<Output = io::Result<()>> + '_ [FlushFuture<'_, Self>]
        where
            Self: Unpin,
        {
            FlushFuture { writer: self }
        }

        #[doc = r#"
            Like [`write`], except that it writes from a slice of buffers.

            Data is copied from each buffer in order, with the final buffer read from possibly
            being only partially consumed. This method must behave as a call to [`write`] with
            the buffers concatenated would.

            The default implementation calls [`write`] with either the first nonempty buffer
            provided, or an empty one if none exists.

            [`write`]: #tymethod.write
        "#]
        fn write_vectored<'a>(
            &'a mut self,
            bufs: &'a [IoSlice<'a>],
        ) -> impl Future<Output = io::Result<usize>> + 'a [WriteVectoredFuture<'a, Self>]
        where
            Self: Unpin,
        {
            WriteVectoredFuture { writer: self, bufs }
        }

        #[doc = r#"
            Writes an entire buffer into the byte stream.

            This method will continuously call [`write`] until there is no more data to be
            written or an error is returned. This method will not return until the entire
            buffer has been successfully written or such an error occurs.

            [`write`]: #tymethod.write

            # Examples

            ```no_run
            # fn main() -> std::io::Result<()> { async_std::task::block_on(async {
            #
            use async_std::fs::File;
            use async_std::prelude::*;

            let mut file = File::create("a.txt").await?;

            file.write_all(b"hello world").await?;
            #
            # Ok(()) }) }
            ```

            [`write`]: #tymethod.write
        "#]
        fn write_all<'a>(
            &'a mut self,
            buf: &'a [u8],
        ) -> impl Future<Output = io::Result<()>> + 'a [WriteAllFuture<'a, Self>]
        where
            Self: Unpin,
        {
            WriteAllFuture { writer: self, buf }
        }

        #[doc = r#"
            Writes a formatted string into this writer, returning any error encountered.

            This method will continuously call [`write`] until there is no more data to be
            written or an error is returned. This future will not resolve until the entire
            buffer has been successfully written or such an error occurs.

            [`write`]: #tymethod.write

            # Examples

            ```no_run
            # fn main() -> std::io::Result<()> { async_std::task::block_on(async {
            #
            use async_std::io::prelude::*;
            use async_std::fs::File;

            let mut buffer = File::create("foo.txt").await?;

            // this call
            write!(buffer, "{:.*}", 2, 1.234567).await?;
            // turns into this:
            buffer.write_fmt(format_args!("{:.*}", 2, 1.234567)).await?;
            #
            # Ok(()) }) }
            ```
        "#]
        fn write_fmt<'a>(
            &'a mut self,
            fmt: std::fmt::Arguments<'_>,
        ) -> impl Future<Output = io::Result<()>> + 'a [WriteFmtFuture<'a, Self>]
        where
            Self: Unpin,
        {
            // In order to not have to implement an async version of `fmt` including private types
            // and all, we convert `Arguments` to a `Result<Vec<u8>>` and pass that to the Future.
            // Doing an owned conversion saves us from juggling references.
            let mut string = String::new();
            let res = std::fmt::write(&mut string, fmt)
                .map(|_| string.into_bytes())
                .map_err(|_| io::Error::new(io::ErrorKind::Other, "formatter error"));
            WriteFmtFuture { writer: self, res: Some(res), buffer: None, amt: 0 }
        }
    }

    impl<T: Write + Unpin + ?Sized> Write for Box<T> {
        fn poll_write(
            self: Pin<&mut Self>,
            cx: &mut Context<'_>,
            buf: &[u8],
        ) -> Poll<io::Result<usize>> {
            unreachable!("this impl only appears in the rendered docs")
        }

        fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
            unreachable!("this impl only appears in the rendered docs")
        }

        fn poll_close(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
            unreachable!("this impl only appears in the rendered docs")
        }
    }

    impl<T: Write + Unpin + ?Sized> Write for &mut T {
        fn poll_write(
            self: Pin<&mut Self>,
            cx: &mut Context<'_>,
            buf: &[u8],
        ) -> Poll<io::Result<usize>> {
            unreachable!("this impl only appears in the rendered docs")
        }

        fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
            unreachable!("this impl only appears in the rendered docs")
        }

        fn poll_close(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
            unreachable!("this impl only appears in the rendered docs")
        }
    }

    impl<P> Write for Pin<P>
    where
        P: DerefMut + Unpin,
        <P as Deref>::Target: Write,
    {
        fn poll_write(
            self: Pin<&mut Self>,
            cx: &mut Context<'_>,
            buf: &[u8],
        ) -> Poll<io::Result<usize>> {
            unreachable!("this impl only appears in the rendered docs")
        }

        fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
            unreachable!("this impl only appears in the rendered docs")
        }

        fn poll_close(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
            unreachable!("this impl only appears in the rendered docs")
        }
    }

    impl Write for Vec<u8> {
        fn poll_write(
            self: Pin<&mut Self>,
            cx: &mut Context<'_>,
            buf: &[u8],
        ) -> Poll<io::Result<usize>> {
            unreachable!("this impl only appears in the rendered docs")
        }

        fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
            unreachable!("this impl only appears in the rendered docs")
        }

        fn poll_close(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
            unreachable!("this impl only appears in the rendered docs")
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    use crate::io::write::WriteExt;
    use crate::task::{Context, Poll};
    use std::pin::Pin;

    use futures::Future;
    use futures_io::{Error, ErrorKind};
    
    struct PartialWriter {
        expected: Vec<u8>,
    }
    impl Write for PartialWriter {
        fn poll_write(
            mut self: Pin<&mut Self>,
            _cx: &mut Context<'_>,
            buf: &[u8],
        ) -> Poll<io::Result<usize>> {
            let write_len = usize::max(1, self.expected.len() / 2);

            let first = &self.expected[..write_len];

            if *first != buf[..write_len] {
                Poll::Ready(Err(Error::new(ErrorKind::Other, "unexpected contents")))
            } else {
                self.expected = self.expected[write_len..].to_owned();
                Poll::Ready(Ok( write_len ))
            }
        }
    
        fn poll_flush(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<io::Result<()>> {
            Poll::Ready(Ok(()))
        }
    
        fn poll_close(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<io::Result<()>> {
            Poll::Ready(Ok(()))
        }
    }

/* 
there is no way (we found) to declare this without either getting 
E0597 -- borrowed value does not live long enough    https://doc.rust-lang.org/error-index.html#E0597
or
E0521 -- Borrowed data escapes outside of closure.   https://doc.rust-lang.org/error-index.html#E0521

or a bunch of other problems
*/

/* E0597: * /
    async fn run_partial_write_test<'a, F, RF>(write_fn: F) -> std::io::Result<()> 
    where
        F: Fn(&'a mut PartialWriter, &str) -> RF,
        RF: Future<Output = crate::io::Result<()>> + 'a,
    {
        let content = "a12345678a";

        let mut partial_writer = PartialWriter{ expected: content.as_bytes().to_owned() };


        (write_fn)(&mut partial_writer, content).await?;

        if partial_writer.expected.len() > 0 {
            Err(Error::new(ErrorKind::Other, "expected content not written"))
        } else {
            Ok(())
        }

        Ok(())
    }

    #[test]
    fn test_partial_write_fmt_2() -> std::io::Result<()> {
        fn write_fn<'a,>(pw: &'a mut PartialWriter, content: &str) -> WriteFmtFuture<'a, &'a mut PartialWriter> {
            write!(&mut pw, "{}", content)
        }

        let x = run_partial_write_test(&write_fn);
        crate::task::block_on(x)
    }
/ **/

    fn run_partial_write_test<'a, RF>(write_fn: fn(&'a mut PartialWriter, &str) -> RF) -> std::io::Result<()>
    where
        RF: Future<Output = crate::io::Result<()>> + 'a,
    {
        let content = "a12345678a";

        let mut partial_writer = PartialWriter{ expected: content.as_bytes().to_owned() };


        crate::task::block_on(write_fn(&mut partial_writer, content))?;

        if partial_writer.expected.len() > 0 {
            Err(Error::new(ErrorKind::Other, "expected content not written"))
        } else {
            Ok(())
        }
    }

    #[test]
    fn test_partial_write_fmt_2() -> std::io::Result<()> {
        fn write_fn<'a>(pw: &'a mut PartialWriter, content: &str) -> WriteFmtFuture<'a, &'a mut PartialWriter> {
            (&mut pw).write_fmt(format_args!("{}", content))
        }

        run_partial_write_test(write_fn)
    }


 #[test]
    fn test_partial_write_fmt() -> std::io::Result<()> {
        async fn run<'a>() -> std::io::Result<()> {
            let a = "a12345678a";

            let mut partial_writer: PartialWriter = PartialWriter{ expected: a.as_bytes().to_owned() };
    
            let x = write!(
                &mut partial_writer, 
                "{}",
                a, 
            );

            x.await?;

            if partial_writer.expected.len() > 0 {
                Err(Error::new(ErrorKind::Other, "expected content not written"))
            } else {
                Ok(())
            }
        }

        crate::task::block_on(run())
    }
    #[test]
    fn test_partial_write() -> std::io::Result<()> {
        async fn run() -> std::io::Result<()> {
            let a = "a12345678a";

            let mut partial_writer = PartialWriter{ expected: a.as_bytes().to_owned() };
    
            partial_writer.write_all(a.as_bytes()).await?;

            if partial_writer.expected.len() > 0 {
                Err(Error::new(ErrorKind::Other, "expected content not written"))
            } else {
                Ok(())
            }
        }

        crate::task::block_on(run())
    }
}