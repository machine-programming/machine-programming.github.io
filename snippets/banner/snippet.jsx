export default () => (
    <React.Suspense fallback={(<div>Loading...</div>)}>
        <RemoteButton />
    </React.Suspense>
);
