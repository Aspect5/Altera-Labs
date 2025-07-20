import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react'

// https://vitejs.dev/config/
export default defineConfig({
  plugins: [react()],
  server: {
    proxy: {
      // This will proxy any request starting with /api to your backend server
      '/api': {
        target: 'http://localhost:5000',
        changeOrigin: true,
        // The incorrect 'rewrite' rule has been removed.
        // Now, a frontend request to '/api/message' will be correctly 
        // proxied to 'http://localhost:5000/api/message'.
      },
    },
  },
})
